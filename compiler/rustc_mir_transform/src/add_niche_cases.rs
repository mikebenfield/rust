//! Turn a SwitchInt over an Rvalue::Discriminant into a SwitchInt over an
//! Rvalue::RelativeDiscriminant, adding extra cases for the potential values
//! representing the dataful variant as needed.
//!
//! This is intended to improve the performance of enums with the niche filling
//! optimization.

use crate::MirPass;
use rustc_middle::mir::*;
use rustc_middle::ty::TyCtxt;
use rustc_target::abi::{TagEncoding, Variants};

use std::iter;

// FIXME - figure out a good value for this, or another way to determine when
// to apply this optimization.
const ALLOWED_EXTRA_BRANCHES: u128 = 20;

pub struct AddNicheCases;

impl<'tcx> MirPass<'tcx> for AddNicheCases {
    fn is_enabled(&self, sess: &rustc_session::Session) -> bool {
        // FIXME - what should be the correct opt level to use here?
        sess.mir_opt_level() >= 1
    }

    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        // FIXME - is there something better we can do here?
        if body.generator.is_some() {
            return;
        }

        let def_id = body.source.def_id();
        let param_env = tcx.param_env(def_id);

        let (bbs, local_decls) = body.basic_blocks_and_local_decls_mut();

        for bb_idx in bbs.indices() {
            let (d, enum_place, assignment_index, targets) = match bbs[bb_idx].terminator().kind {
                TerminatorKind::SwitchInt {
                    discr: Operand::Copy(ref d) | Operand::Move(ref d),
                    ref targets,
                    ..
                } => {
                    if targets.iter().len() <= 1 {
                        continue;
                    }

                    let otherwise_is_unreachable = {
                        match bbs[targets.otherwise()].terminator().kind {
                            TerminatorKind::Unreachable => true,
                            _ => false,
                        }
                    };

                    if targets.iter().len() == 2 && otherwise_is_unreachable {
                        continue;
                    }

                    let mut enum_place_maybe = None;
                    let mut assignment_index_maybe = None;
                    for (i, stmt) in bbs[bb_idx].statements.iter().enumerate().rev() {
                        match stmt.kind {
                            StatementKind::Assign(box (ref place, ref rvalue)) if *place == *d => {
                                if let Rvalue::Discriminant(enum_place) = rvalue {
                                    enum_place_maybe = Some(enum_place);
                                    assignment_index_maybe = Some(i);
                                }
                                break;
                            }
                            _ => {}
                        }
                    }
                    if let (Some(enum_place), Some(assignment_index)) =
                        (enum_place_maybe, assignment_index_maybe)
                    {
                        (*d, *enum_place, assignment_index, targets)
                    } else {
                        continue;
                    }
                }

                _ => continue,
            };

            let enum_ty = enum_place.ty(local_decls, tcx).ty;
            let d_ty = d.ty(local_decls, tcx).ty;
            let enum_ty_and_layout = match tcx.layout_of(param_env.and(enum_ty)) {
                Ok(ty_and_layout) => ty_and_layout,
                _ => continue,
            };

            let (tag, tag_encoding) = match enum_ty_and_layout.layout.variants() {
                Variants::Multiple { tag, ref tag_encoding, .. } => (tag, tag_encoding),

                _ => continue,
            };

            let (dataful_variant, niche_start, niche_variants) = match tag_encoding {
                TagEncoding::Niche { dataful_variant, niche_start, niche_variants, .. } => {
                    (*dataful_variant, *niche_start, niche_variants)
                }

                _ => continue,
            };

            let niche_variants_count_m1 =
                niche_variants.end().as_u32() - niche_variants.start().as_u32();

            let niche_variants_count = niche_variants_count_m1 as u128 + 1;

            let dataful_bb = {
                let found = targets.iter().find(|(v, _)| *v == dataful_variant.as_u32() as u128);
                if let Some((_, b)) = found {
                    b
                } else {
                    // The dataful variant doesn't appear in the target blocks anyway.
                    continue;
                }
            };

            let valid_range = tag.valid_range;
            let max_value = tag.value.size(&tcx).unsigned_int_max();
            let valid_values_count_m1 = valid_range.end.wrapping_sub(valid_range.start);

            let needed_extra_branches_m1 = valid_values_count_m1
                .checked_sub(niche_variants_count)
                .expect("Can't have fewer variants than valid values in a niche");
            if needed_extra_branches_m1 > ALLOWED_EXTRA_BRANCHES - 1 {
                continue;
            }

            let first = if niche_start == valid_range.start {
                // valid and non-variant values come at the end
                niche_variants.end().as_u32() as u128 + 1
            } else {
                // valid and non-variant values come at the beginning
                let last = (niche_variants.start().as_u32() as u128).wrapping_sub(1);
                let first = last.wrapping_sub(needed_extra_branches_m1);
                first
            };

            let needed_extra_branches = needed_extra_branches_m1 as usize + 1;
            let new_values = iter::successors(Some(first), |v| Some(v.wrapping_add(1)))
                .map(|v| v & max_value)
                .take(needed_extra_branches);
            let new_targets = iter::repeat(dataful_bb);
            let new_values_targets = new_values.zip(new_targets);

            let old_iter = targets.iter().filter(|(v, _)| *v != dataful_variant.as_u32() as u128);
            let all_values_targets = new_values_targets.chain(old_iter).map(|(v, t)| {
                (v.wrapping_sub(niche_variants.start().as_u32() as u128) & max_value, t)
            });
            let otherwise = targets.otherwise();

            let new_targets = SwitchTargets::new(all_values_targets, otherwise);
            let source_info = bbs[bb_idx].terminator().source_info;

            let span = local_decls[d.local].source_info.span;
            let fake_d: Place<'_> = local_decls.push(LocalDecl::new(d_ty, span)).into();
            let assignment = Statement {
                source_info: bbs[bb_idx].statements[assignment_index].source_info,
                kind: StatementKind::Assign(Box::new((
                    fake_d,
                    Rvalue::RelativeDiscriminant(enum_place),
                ))),
            };

            let new_terminator = Terminator {
                source_info,
                kind: TerminatorKind::SwitchInt {
                    discr: Operand::Copy(fake_d),
                    switch_ty: d_ty,
                    targets: new_targets,
                },
            };

            bbs[bb_idx].statements.push(assignment);
            bbs[bb_idx].terminator = Some(new_terminator);
        }
    }
}
