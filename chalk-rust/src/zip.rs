use errors::*;
use ir::*;
use solve::environment::{Environment, InEnvironment};
use std::sync::Arc;

pub trait Zipper {
    fn zip_tys(&mut self, a: &Ty, b: &Ty) -> Result<()>;
    fn zip_lifetimes(&mut self, a: &Lifetime, b: &Lifetime) -> Result<()>;
}

impl<'f, Z: Zipper> Zipper for &'f mut Z {
    fn zip_tys(&mut self, a: &Ty, b: &Ty) -> Result<()> {
        (**self).zip_tys(a, b)
    }

    fn zip_lifetimes(&mut self, a: &Lifetime, b: &Lifetime) -> Result<()> {
        (**self).zip_lifetimes(a, b)
    }
}

pub trait Zip {
    fn zip_with<Z: Zipper>(zipper: &mut Z, a: &Self, b: &Self) -> Result<()>;
}

impl<'a, T: Zip> Zip for &'a T {
    fn zip_with<Z: Zipper>(zipper: &mut Z, a: &Self, b: &Self) -> Result<()> {
        <T as Zip>::zip_with(zipper, a, b)
    }
}

impl<T: Zip> Zip for Vec<T> {
    fn zip_with<Z: Zipper>(zipper: &mut Z, a: &Self, b: &Self) -> Result<()> {
        if a.len() != b.len() {
            bail!("cannot zip arrays of different lengths: {} vs {}",
                  a.len(), b.len());
        }

        for (a_elem, b_elem) in a.iter().zip(b) {
            Zip::zip_with(zipper, a_elem, b_elem)?;
        }

        Ok(())
    }
}

impl<T: Zip> Zip for Arc<T> {
    fn zip_with<Z: Zipper>(zipper: &mut Z, a: &Self, b: &Self) -> Result<()> {
        <T as Zip>::zip_with(zipper, a, b)
    }
}

impl<T: Zip, U: Zip> Zip for (T, U) {
    fn zip_with<Z: Zipper>(zipper: &mut Z, a: &Self, b: &Self) -> Result<()> {
        Zip::zip_with(zipper, &a.0, &b.0)?;
        Zip::zip_with(zipper, &a.1, &b.1)?;
        Ok(())
    }
}

impl<T: Zip, L: Zip> Zip for ParameterKind<T, L> {
    fn zip_with<Z: Zipper>(zipper: &mut Z, a: &Self, b: &Self) -> Result<()> {
        match (a, b) {
            (&ParameterKind::Ty(ref a), &ParameterKind::Ty(ref b)) => Zip::zip_with(zipper, a, b),
            (&ParameterKind::Lifetime(ref a), &ParameterKind::Lifetime(ref b)) => Zip::zip_with(zipper, a, b),
            (&ParameterKind::Ty(_), &ParameterKind::Lifetime(_)) |
            (&ParameterKind::Lifetime(_), &ParameterKind::Ty(_)) => {
                panic!("zipping things of mixed kind")
            }
        }
    }
}

impl Zip for Ty {
    fn zip_with<Z: Zipper>(zipper: &mut Z, a: &Self, b: &Self) -> Result<()> {
        zipper.zip_tys(a, b)
    }
}

impl Zip for Lifetime {
    fn zip_with<Z: Zipper>(zipper: &mut Z, a: &Self, b: &Self) -> Result<()> {
        zipper.zip_lifetimes(a, b)
    }
}

impl Zip for ItemId {
    fn zip_with<Z: Zipper>(_zipper: &mut Z, a: &Self, b: &Self) -> Result<()> {
        if a != b {
            bail!("cannot zip `{:?}` and `{:?}`", a, b)
        }
        Ok(())
    }
}

impl Zip for TypeName {
    fn zip_with<Z: Zipper>(_zipper: &mut Z, a: &Self, b: &Self) -> Result<()> {
        if a != b {
            bail!("cannot zip `{:?}` and `{:?}`", a, b)
        }
        Ok(())
    }
}

impl Zip for Identifier {
    fn zip_with<Z: Zipper>(_zipper: &mut Z, a: &Self, b: &Self) -> Result<()> {
        if a != b {
            bail!("cannot zip `{:?}` and `{:?}`", a, b)
        }
        Ok(())
    }
}

impl Zip for TraitRef {
    fn zip_with<Z: Zipper>(zipper: &mut Z, a: &Self, b: &Self) -> Result<()> {
        Zip::zip_with(zipper, &a.trait_id, &b.trait_id)?;
        Zip::zip_with(zipper, &a.parameters, &b.parameters)?;
        Ok(())
    }
}

impl<T: Zip> Zip for InEnvironment<T> {
    fn zip_with<Z: Zipper>(zipper: &mut Z, a: &Self, b: &Self) -> Result<()> {
        Zip::zip_with(zipper, &a.environment, &b.environment)?;
        Zip::zip_with(zipper, &a.goal, &b.goal)?;
        Ok(())
    }
}

impl Zip for ApplicationTy {
    fn zip_with<Z: Zipper>(zipper: &mut Z, a: &Self, b: &Self) -> Result<()> {
        Zip::zip_with(zipper, &a.name, &b.name)?;
        Zip::zip_with(zipper, &a.parameters, &b.parameters)?;
        Ok(())
    }
}

impl Zip for ProjectionTy {
    fn zip_with<Z: Zipper>(zipper: &mut Z, a: &Self, b: &Self) -> Result<()> {
        Zip::zip_with(zipper, &a.trait_ref, &b.trait_ref)?;
        Zip::zip_with(zipper, &a.name, &b.name)?;
        Ok(())
    }
}

impl Zip for Normalize {
    fn zip_with<Z: Zipper>(zipper: &mut Z, a: &Self, b: &Self) -> Result<()> {
        Zip::zip_with(zipper, &a.projection, &b.projection)?;
        Zip::zip_with(zipper, &a.ty, &b.ty)?;
        Ok(())
    }
}

impl Zip for Environment {
    fn zip_with<Z: Zipper>(zipper: &mut Z, a: &Self, b: &Self) -> Result<()> {
        assert_eq!(a.universe, b.universe); // it's wrong to zip 2 env's with distinct universes!
        assert_eq!(a.clauses.len(), b.clauses.len()); // or different numbers of clauses
        Zip::zip_with(zipper, &a.clauses, &b.clauses)?;
        Ok(())
    }
}

impl Zip for WhereClause {
    fn zip_with<Z: Zipper>(zipper: &mut Z, a: &Self, b: &Self) -> Result<()> {
        match (a, b) {
            (&WhereClause::Implemented(ref a), &WhereClause::Implemented(ref b)) => {
                Zip::zip_with(zipper, a, b)
            }
            (&WhereClause::Normalize(ref a), &WhereClause::Normalize(ref b)) => {
                Zip::zip_with(zipper, a, b)
            }
            (&WhereClause::Implemented(_), &WhereClause::Normalize(_)) |
            (&WhereClause::Normalize(_), &WhereClause::Implemented(_)) => {
                bail!("cannot zip where-clauses `{:?}` and `{:?}`", a, b)
            }
        }
    }
}

impl Zip for WhereClauseGoal {
    fn zip_with<Z: Zipper>(zipper: &mut Z, a: &Self, b: &Self) -> Result<()> {
        match (a, b) {
            (&WhereClauseGoal::Implemented(ref a), &WhereClauseGoal::Implemented(ref b)) => {
                Zip::zip_with(zipper, a, b)
            }
            (&WhereClauseGoal::Normalize(ref a), &WhereClauseGoal::Normalize(ref b)) => {
                Zip::zip_with(zipper, a, b)
            }
            (&WhereClauseGoal::Implemented(_), &WhereClauseGoal::Normalize(_)) |
            (&WhereClauseGoal::Normalize(_), &WhereClauseGoal::Implemented(_)) => {
                bail!("cannot zip where-clause-goals `{:?}` and `{:?}`", a, b)
            }
        }
    }
}