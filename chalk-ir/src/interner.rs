use crate::AliasTy;
use crate::ApplicationTy;
use crate::AssocTypeId;
use crate::Goal;
use crate::GoalData;
use crate::Goals;
use crate::Lifetime;
use crate::LifetimeData;
use crate::Parameter;
use crate::ParameterData;
use crate::ProgramClauseImplication;
use crate::SeparatorTraitRef;
use crate::StructId;
use crate::Substitution;
use crate::TraitId;
use crate::Ty;
use crate::TyData;
use chalk_engine::context::Context;
use chalk_engine::ExClause;
use std::fmt::{self, Debug};
use std::hash::Hash;
use std::marker::PhantomData;
use std::sync::Arc;

#[cfg(any(test, feature = "default-interner"))]
pub use default::*;

/// A "interner" encapsulates the concrete representation of
/// certain "core types" from chalk-ir. All the types in chalk-ir are
/// parameterized by a `I: Interner`, and so (e.g.) if they want to
/// store a type, they don't store a `Ty<I>` instance directly, but
/// rather prefer a `Ty<I>`. You can think of `I::Type` as the
/// interned representation (and, indeed, it may well be an interned
/// pointer, e.g. in rustc).
///
/// Type families allow chalk to be embedded in different contexts
/// where the concrete representation of core types varies. They also
/// allow us to write generic code that reasons about multiple
/// distinct sets of types by using distinct generic type parameters
/// (e.g., `SourceI` and `TargetI`) -- even if those type parameters
/// wind up being mapped to the same underlying type families in the
/// end.
pub trait Interner: Debug + Copy + Eq + Ord + Hash {
    /// "Interned" representation of types.  In normal user code,
    /// `Self::InternedType` is not referenced Instead, we refer to
    /// `Ty<Self>`, which wraps this type.
    ///
    /// An `InternedType` must be something that can be created from a
    /// `TyData` (by the [`intern_ty`] method) and then later
    /// converted back (by the [`ty_data`] method). The interned form
    /// must also introduce indirection, either via a `Box`, `&`, or
    /// other pointer type.
    type InternedType: Debug + Clone + Eq + Hash;

    /// "Interned" representation of lifetimes.  In normal user code,
    /// `Self::InternedLifetime` is not referenced Instead, we refer to
    /// `Lifetime<Self>`, which wraps this type.
    ///
    /// An `InternedLifetime` must be something that can be created
    /// from a `LifetimeData` (by the [`intern_lifetime`] method) and
    /// then later converted back (by the [`lifetime_data`] method).
    type InternedLifetime: Debug + Clone + Eq + Hash;

    /// "Interned" representation of a "generic parameter", which can
    /// be either a type or a lifetime.  In normal user code,
    /// `Self::InternedParameter` is not referenced. Instead, we refer to
    /// `Parameter<Self>`, which wraps this type.
    ///
    /// An `InternedType` is created by `intern_parameter` and can be
    /// converted back to its underlying data via `parameter_data`.
    type InternedParameter: Debug + Clone + Eq + Hash;

    /// "Interned" representation of a "goal".  In normal user code,
    /// `Self::InternedGoal` is not referenced. Instead, we refer to
    /// `Goal<Self>`, which wraps this type.
    ///
    /// An `InternedGoal` is created by `intern_goal` and can be
    /// converted back to its underlying data via `goal_data`.
    type InternedGoal: Debug + Clone + Eq + Hash;

    /// "Interned" representation of a list of goals.  In normal user code,
    /// `Self::InternedGoals` is not referenced. Instead, we refer to
    /// `Goals<Self>`, which wraps this type.
    ///
    /// An `InternedGoals` is created by `intern_goals` and can be
    /// converted back to its underlying data via `goals_data`.
    type InternedGoals: Debug + Clone + Eq + Hash;

    /// "Interned" representation of a "substitution".  In normal user code,
    /// `Self::InternedSubstitution` is not referenced. Instead, we refer to
    /// `Substitution<Self>`, which wraps this type.
    ///
    /// An `InternedSubstitution` is created by `intern_substitution` and can be
    /// converted back to its underlying data via `substitution_data`.
    type InternedSubstitution: Debug + Clone + Eq + Hash;

    /// The core "id" type used for struct-ids and the like.
    type DefId: Debug + Copy + Eq + Ord + Hash;

    type Identifier: Debug + Clone + Eq + Hash;

    /// Prints the debug representation of a type-kind-id. To get good
    /// results, this requires inspecting TLS, and is difficult to
    /// code without reference to a specific interner (and hence
    /// fully known types).
    ///
    /// Returns `None` to fallback to the default debug output (e.g.,
    /// if no info about current program is available from TLS).
    fn debug_struct_id(
        struct_id: StructId<Self>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Option<fmt::Result>;

    /// Prints the debug representation of a type-kind-id. To get good
    /// results, this requires inspecting TLS, and is difficult to
    /// code without reference to a specific interner (and hence
    /// fully known types).
    ///
    /// Returns `None` to fallback to the default debug output (e.g.,
    /// if no info about current program is available from TLS).
    fn debug_trait_id(trait_id: TraitId<Self>, fmt: &mut fmt::Formatter<'_>)
        -> Option<fmt::Result>;

    /// Prints the debug representation of a type-kind-id. To get good
    /// results, this requires inspecting TLS, and is difficult to
    /// code without reference to a specific interner (and hence
    /// fully known types).
    fn debug_assoc_type_id(
        type_id: AssocTypeId<Self>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Option<fmt::Result>;

    /// Prints the debug representation of an alias. To get good
    /// results, this requires inspecting TLS, and is difficult to
    /// code without reference to a specific interner (and hence
    /// fully known types).
    ///
    /// Returns `None` to fallback to the default debug output (e.g.,
    /// if no info about current program is available from TLS).
    fn debug_alias(alias: &AliasTy<Self>, fmt: &mut fmt::Formatter<'_>) -> Option<fmt::Result>;

    /// Prints the debug representation of an type. To get good
    /// results, this requires inspecting TLS, and is difficult to
    /// code without reference to a specific interner (and hence
    /// fully known types).
    ///
    /// Returns `None` to fallback to the default debug output (e.g.,
    /// if no info about current program is available from TLS).
    fn debug_ty(ty: &Ty<Self>, fmt: &mut fmt::Formatter<'_>) -> Option<fmt::Result>;

    /// Prints the debug representation of an lifetime. To get good
    /// results, this requires inspecting TLS, and is difficult to
    /// code without reference to a specific interner (and hence
    /// fully known types).
    ///
    /// Returns `None` to fallback to the default debug output (e.g.,
    /// if no info about current program is available from TLS).
    fn debug_lifetime(
        lifetime: &Lifetime<Self>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Option<fmt::Result>;

    /// Prints the debug representation of an parameter. To get good
    /// results, this requires inspecting TLS, and is difficult to
    /// code without reference to a specific interner (and hence
    /// fully known types).
    ///
    /// Returns `None` to fallback to the default debug output (e.g.,
    /// if no info about current program is available from TLS).
    fn debug_parameter(
        parameter: &Parameter<Self>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Option<fmt::Result>;

    /// Prints the debug representation of an goal. To get good
    /// results, this requires inspecting TLS, and is difficult to
    /// code without reference to a specific interner (and hence
    /// fully known types).
    ///
    /// Returns `None` to fallback to the default debug output (e.g.,
    /// if no info about current program is available from TLS).
    fn debug_goal(goal: &Goal<Self>, fmt: &mut fmt::Formatter<'_>) -> Option<fmt::Result>;

    /// Prints the debug representation of a list of goals. To get good
    /// results, this requires inspecting TLS, and is difficult to
    /// code without reference to a specific interner (and hence
    /// fully known types).
    ///
    /// Returns `None` to fallback to the default debug output (e.g.,
    /// if no info about current program is available from TLS).
    fn debug_goals(goals: &Goals<Self>, fmt: &mut fmt::Formatter<'_>) -> Option<fmt::Result>;

    /// Prints the debug representation of a ProgramClauseImplication. To get good
    /// results, this requires inspecting TLS, and is difficult to
    /// code without reference to a specific interner (and hence
    /// fully known types).
    ///
    /// Returns `None` to fallback to the default debug output (e.g.,
    /// if no info about current program is available from TLS).
    fn debug_program_clause_implication(
        pci: &ProgramClauseImplication<Self>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Option<fmt::Result>;

    /// Prints the debug representation of an ApplicationTy. To get good
    /// results, this requires inspecting TLS, and is difficult to
    /// code without reference to a specific interner (and hence
    /// fully known types).
    ///
    /// Returns `None` to fallback to the default debug output (e.g.,
    /// if no info about current program is available from TLS).
    fn debug_application_ty(
        application_ty: &ApplicationTy<Self>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Option<fmt::Result>;

    /// Prints the debug representation of a Substitution. To get good
    /// results, this requires inspecting TLS, and is difficult to
    /// code without reference to a specific interner (and hence
    /// fully known types).
    ///
    /// Returns `None` to fallback to the default debug output (e.g.,
    /// if no info about current program is available from TLS).
    fn debug_substitution(
        substitution: &Substitution<Self>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Option<fmt::Result>;

    /// Prints the debug representation of a SeparatorTraitRef. To get good
    /// results, this requires inspecting TLS, and is difficult to
    /// code without reference to a specific interner (and hence
    /// fully known types).
    ///
    /// Returns `None` to fallback to the default debug output (e.g.,
    /// if no info about current program is available from TLS).
    fn debug_separator_trait_ref(
        separator_trait_ref: &SeparatorTraitRef<Self>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Option<fmt::Result>;

    /// Create an "interned" type from `ty`. This is not normally
    /// invoked directly; instead, you invoke `TyData::intern` (which
    /// will ultimately call this method).
    fn intern_ty(&self, ty: TyData<Self>) -> Self::InternedType;

    /// Lookup the `TyData` from an interned type.
    fn ty_data<'a>(&self, ty: &'a Self::InternedType) -> &'a TyData<Self>;

    /// Create an "interned" lifetime from `lifetime`. This is not
    /// normally invoked directly; instead, you invoke
    /// `LifetimeData::intern` (which will ultimately call this
    /// method).
    fn intern_lifetime(&self, lifetime: LifetimeData<Self>) -> Self::InternedLifetime;

    /// Lookup the `LifetimeData` that was interned to create a `InternedLifetime`.
    fn lifetime_data<'a>(&self, lifetime: &'a Self::InternedLifetime) -> &'a LifetimeData<Self>;

    /// Create an "interned" parameter from `data`. This is not
    /// normally invoked directly; instead, you invoke
    /// `ParameterData::intern` (which will ultimately call this
    /// method).
    fn intern_parameter(&self, data: ParameterData<Self>) -> Self::InternedParameter;

    /// Lookup the `LifetimeData` that was interned to create a `InternedLifetime`.
    fn parameter_data<'a>(&self, lifetime: &'a Self::InternedParameter) -> &'a ParameterData<Self>;

    /// Create an "interned" goal from `data`. This is not
    /// normally invoked directly; instead, you invoke
    /// `GoalData::intern` (which will ultimately call this
    /// method).
    fn intern_goal(&self, data: GoalData<Self>) -> Self::InternedGoal;

    /// Lookup the `GoalData` that was interned to create a `InternedGoal`.
    fn goal_data<'a>(&self, goal: &'a Self::InternedGoal) -> &'a GoalData<Self>;

    /// Create an "interned" goals from `data`. This is not
    /// normally invoked directly; instead, you invoke
    /// `GoalsData::intern` (which will ultimately call this
    /// method).
    fn intern_goals(&self, data: impl IntoIterator<Item = Goal<Self>>) -> Self::InternedGoals;

    /// Lookup the `GoalsData` that was interned to create a `InternedGoals`.
    fn goals_data<'a>(&self, goals: &'a Self::InternedGoals) -> &'a [Goal<Self>];

    /// Create an "interned" substitution from `data`. This is not
    /// normally invoked directly; instead, you invoke
    /// `SubstitutionData::intern` (which will ultimately call this
    /// method).
    fn intern_substitution<E>(
        &self,
        data: impl IntoIterator<Item = Result<Parameter<Self>, E>>,
    ) -> Result<Self::InternedSubstitution, E>;

    /// Lookup the `SubstitutionData` that was interned to create a `InternedSubstitution`.
    fn substitution_data<'a>(
        &self,
        substitution: &'a Self::InternedSubstitution,
    ) -> &'a [Parameter<Self>];
}

pub trait TargetInterner<I: Interner>: Interner {
    fn transfer_def_id(def_id: I::DefId) -> Self::DefId;
}

impl<I: Interner> TargetInterner<I> for I {
    fn transfer_def_id(def_id: I::DefId) -> Self::DefId {
        def_id
    }
}

/// Implemented by types that have an associated interner (which
/// are virtually all of the types in chalk-ir, for example).
/// This lets us map from a type like `Ty<I>` to the parameter `I`.
///
/// It's particularly useful for writing `Fold` impls for generic types like
/// `Binder<T>`, since it allows us to figure out the interner of `T`.
pub trait HasInterner {
    type Interner: Interner;
}

#[cfg(any(test, feature = "default-interner"))]
mod default {
    use super::*;
    use crate::tls;
    use lalrpop_intern::InternedString;
    use std::fmt;

    pub type Identifier = InternedString;

    #[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct RawId {
        pub index: u32,
    }

    impl Debug for RawId {
        fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(fmt, "#{}", self.index)
        }
    }

    /// The default "interner" and the only interner used by chalk
    /// itself. In this interner, no interning actually occurs.
    #[derive(Debug, Copy, Clone, Hash, PartialOrd, Ord, PartialEq, Eq)]
    pub struct ChalkIr;

    impl Interner for ChalkIr {
        type InternedType = Arc<TyData<ChalkIr>>;
        type InternedLifetime = LifetimeData<ChalkIr>;
        type InternedParameter = ParameterData<ChalkIr>;
        type InternedGoal = Arc<GoalData<ChalkIr>>;
        type InternedGoals = Vec<Goal<ChalkIr>>;
        type InternedSubstitution = Vec<Parameter<ChalkIr>>;
        type DefId = RawId;
        type Identifier = Identifier;

        fn debug_struct_id(
            type_kind_id: StructId<ChalkIr>,
            fmt: &mut fmt::Formatter<'_>,
        ) -> Option<fmt::Result> {
            tls::with_current_program(|prog| Some(prog?.debug_struct_id(type_kind_id, fmt)))
        }

        fn debug_trait_id(
            type_kind_id: TraitId<ChalkIr>,
            fmt: &mut fmt::Formatter<'_>,
        ) -> Option<fmt::Result> {
            tls::with_current_program(|prog| Some(prog?.debug_trait_id(type_kind_id, fmt)))
        }

        fn debug_assoc_type_id(
            id: AssocTypeId<ChalkIr>,
            fmt: &mut fmt::Formatter<'_>,
        ) -> Option<fmt::Result> {
            tls::with_current_program(|prog| Some(prog?.debug_assoc_type_id(id, fmt)))
        }

        fn debug_alias(
            alias: &AliasTy<ChalkIr>,
            fmt: &mut fmt::Formatter<'_>,
        ) -> Option<fmt::Result> {
            tls::with_current_program(|prog| Some(prog?.debug_alias(alias, fmt)))
        }

        fn debug_ty(ty: &Ty<ChalkIr>, fmt: &mut fmt::Formatter<'_>) -> Option<fmt::Result> {
            tls::with_current_program(|prog| Some(prog?.debug_ty(ty, fmt)))
        }

        fn debug_lifetime(
            lifetime: &Lifetime<ChalkIr>,
            fmt: &mut fmt::Formatter<'_>,
        ) -> Option<fmt::Result> {
            tls::with_current_program(|prog| Some(prog?.debug_lifetime(lifetime, fmt)))
                .or_else(|| Some(write!(fmt, "{:?}", lifetime.interned)))
        }

        fn debug_parameter(
            parameter: &Parameter<ChalkIr>,
            fmt: &mut fmt::Formatter<'_>,
        ) -> Option<fmt::Result> {
            tls::with_current_program(|prog| Some(prog?.debug_parameter(parameter, fmt)))
        }

        fn debug_goal(goal: &Goal<ChalkIr>, fmt: &mut fmt::Formatter<'_>) -> Option<fmt::Result> {
            tls::with_current_program(|prog| Some(prog?.debug_goal(goal, fmt)))
        }

        fn debug_goals(
            goals: &Goals<ChalkIr>,
            fmt: &mut fmt::Formatter<'_>,
        ) -> Option<fmt::Result> {
            tls::with_current_program(|prog| Some(prog?.debug_goals(goals, fmt)))
        }

        fn debug_program_clause_implication(
            pci: &ProgramClauseImplication<ChalkIr>,
            fmt: &mut fmt::Formatter<'_>,
        ) -> Option<fmt::Result> {
            tls::with_current_program(|prog| Some(prog?.debug_program_clause_implication(pci, fmt)))
        }

        fn debug_application_ty(
            application_ty: &ApplicationTy<ChalkIr>,
            fmt: &mut fmt::Formatter<'_>,
        ) -> Option<fmt::Result> {
            tls::with_current_program(|prog| Some(prog?.debug_application_ty(application_ty, fmt)))
        }

        fn debug_substitution(
            substitution: &Substitution<ChalkIr>,
            fmt: &mut fmt::Formatter<'_>,
        ) -> Option<fmt::Result> {
            tls::with_current_program(|prog| Some(prog?.debug_substitution(substitution, fmt)))
        }

        fn debug_separator_trait_ref(
            separator_trait_ref: &SeparatorTraitRef<ChalkIr>,
            fmt: &mut fmt::Formatter<'_>,
        ) -> Option<fmt::Result> {
            tls::with_current_program(|prog| {
                Some(prog?.debug_separator_trait_ref(separator_trait_ref, fmt))
            })
        }

        fn intern_ty(&self, ty: TyData<ChalkIr>) -> Arc<TyData<ChalkIr>> {
            Arc::new(ty)
        }

        fn ty_data<'a>(&self, ty: &'a Arc<TyData<ChalkIr>>) -> &'a TyData<Self> {
            ty
        }

        fn intern_lifetime(&self, lifetime: LifetimeData<ChalkIr>) -> LifetimeData<ChalkIr> {
            lifetime
        }

        fn lifetime_data<'a>(
            &self,
            lifetime: &'a LifetimeData<ChalkIr>,
        ) -> &'a LifetimeData<ChalkIr> {
            lifetime
        }

        fn intern_parameter(&self, parameter: ParameterData<ChalkIr>) -> ParameterData<ChalkIr> {
            parameter
        }

        fn parameter_data<'a>(
            &self,
            parameter: &'a ParameterData<ChalkIr>,
        ) -> &'a ParameterData<ChalkIr> {
            parameter
        }

        fn intern_goal(&self, goal: GoalData<ChalkIr>) -> Arc<GoalData<ChalkIr>> {
            Arc::new(goal)
        }

        fn goal_data<'a>(&self, goal: &'a Arc<GoalData<ChalkIr>>) -> &'a GoalData<ChalkIr> {
            goal
        }

        fn intern_goals(
            &self,
            data: impl IntoIterator<Item = Goal<ChalkIr>>,
        ) -> Vec<Goal<ChalkIr>> {
            data.into_iter().collect()
        }

        fn goals_data<'a>(&self, goals: &'a Vec<Goal<ChalkIr>>) -> &'a [Goal<ChalkIr>] {
            goals
        }

        fn intern_substitution<E>(
            &self,
            data: impl IntoIterator<Item = Result<Parameter<ChalkIr>, E>>,
        ) -> Result<Vec<Parameter<ChalkIr>>, E> {
            data.into_iter().collect()
        }

        fn substitution_data<'a>(
            &self,
            substitution: &'a Vec<Parameter<ChalkIr>>,
        ) -> &'a [Parameter<ChalkIr>] {
            substitution
        }
    }

    impl HasInterner for ChalkIr {
        type Interner = ChalkIr;
    }
}

impl<T: HasInterner> HasInterner for [T] {
    type Interner = T::Interner;
}

impl<T: HasInterner> HasInterner for Vec<T> {
    type Interner = T::Interner;
}

impl<T: HasInterner> HasInterner for Box<T> {
    type Interner = T::Interner;
}

impl<T: HasInterner> HasInterner for Arc<T> {
    type Interner = T::Interner;
}

impl<T: HasInterner + ?Sized> HasInterner for &T {
    type Interner = T::Interner;
}

impl<I: Interner> HasInterner for PhantomData<I> {
    type Interner = I;
}

impl<A, B, I> HasInterner for (A, B)
where
    A: HasInterner<Interner = I>,
    B: HasInterner<Interner = I>,
    I: Interner,
{
    type Interner = I;
}

impl<C: HasInterner + Context> HasInterner for ExClause<C> {
    type Interner = <C as HasInterner>::Interner;
}
