Alb depends on the following 2 external libraries:

1. indentation-core
2. indentation-parsec

However, they have not been maintained on hackage in the recent past.
As a workaround they have been added here.

Incase you need to add more libraries (hackage packages),
you can add a new folder under `alb/libraries` and then add the package path in `alb/cabal.project`
under `packages` stanza. Don't forget to add the dependency in `alb/alb.cabal`
