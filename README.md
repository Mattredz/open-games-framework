# Open Games Framework

A dependently typed framework for **compositional game theory** built in **Idris 2**. This project models games and their equilibria using **parameterized dependent lenses**, a category-theoretic abstraction that provides both mathematical rigor and practical expressiveness.

## Overview

The Open Games Framework provides a principled approach to game-theoretic modeling by leveraging dependent types and optics. Rather than treating games as monolithic structures, this framework enables you to build complex games from smaller, verifiable components—much like composing functions in functional programming.

### Key Features

- **Dependent Types for Correctness**: Idris 2's dependent type system ensures that game structures are constructed correctly by design, catching errors at compile-time rather than runtime.
- **Parameterized Dependent Lenses**: The core abstraction enables bidirectional transformations between game states with internal fibration structure, supporting both forward game evolution and backward payoff propagation.
- **Compositional Game Construction**: Build complex games by composing simpler lenses using categorical operators. The framework provides composition operators (sequential, parallel, and branching) that preserve game-theoretic properties.
- **Automatic Equilibrium Computation**: Define games and their player rationality rules, then automatically compute Nash equilibria, Hicksian equilibria, and other solution concepts.
- **Real Game Examples**: Includes implementations of classic game-theoretic scenarios like the Prisoner's Dilemma and Ultimatum Game, demonstrating how to model equilibria and strategic behavior.

## Architecture

The framework is organized into several modular components:

### Core Modules

- **Lenses.DTypes**: Defines dependent type structures and fibrations that form the foundation for game representations.
- **Lenses.ParaDLens**: Implements parameterized dependent lenses, the central abstraction for modeling game transformations.
- **Lenses.Operators**: Provides categorical composition operators for combining lenses (sequential `>>>`, parallel `****`, sum `++++`).
- **Lenses.States**: Abstractions for viewing dependent lenses as stateful computations and observations.
- **GameTheory.Core**: Defines `Player`, `Arena`, and `Game` types. Implements automatic `Equilibrium` computation.
- **GameTheory.Combinators**: Advanced combinators including reparameterization, lifting for reverse differentiation, and the Nash composition operator (`$$`).

### Examples

- **GameTheory.Examples.PrisonerDilemma**: Classic two-player simultaneous game demonstrating Nash and Hicksian equilibria.
- **GameTheory.Examples.UltimatumGame**: Sequential bargaining game showing how to model subgame perfect equilibrium.

## Installation & Setup

### Prerequisites

- **Nix** (recommended for reproducible builds)
- **Idris 2** (version 0.7.0 or later)
- **GMP**, **libffi**, and **zlib** libraries

### Quick Start with Nix

The project includes a `flake.nix` configuration for seamless development environment setup:

```bash
# Clone the repository
git clone <repository-url>
cd optics-game-theory

# Enter the development environment
nix flake enter

# (Inside the environment) Build the project
idris2 -p tesi
```

### Manual Setup

If not using Nix, ensure Idris 2 is installed, then:

```bash
# Build the project
idris2 -p tesi

# Run equilibrium computation (example)
idris2 --exec 'printLn PDNashE' src/GameTheory/Examples/PrisonerDilemma.idr
```

## Usage Examples

### Defining a Simple Game

```idris
-- Define action space
data MyAction = Action1 | Action2

-- Define payoff function
payoffFun : MyAction -> Int
payoffFun Action1 = 5
payoffFun Action2 = 3

-- Create game structure
myGame : Game (MyAction ** const Int) DUnit (MyAction ** const Int)
myGame = MkGame corner (scalarToState ()) (FunToCoState payoffFun)

-- Compute equilibrium (assuming MyAction is Listable)
myEquilibrium : List MyAction
myEquilibrium = Equilibrium myGame Argmax
```

## Core Concepts

### Parameterized Dependent Lenses

A `ParaDLens pq xs yr` represents a bidirectional transformation:
- **Forward** (`play`): Transforms source `xs` to target `yr` given parameter `pq`
- **Backward** (`coplay`): Updates source observations and parameters given target feedback

This structure naturally encodes game dynamics: the forward direction represents how players' strategies produce outcomes, while the backward direction represents how payoffs influence strategic choices.

### Dependent Types & Fibrations

Rather than fixed types, the framework uses **dependent pairs** `(X : Type ** X -> Type)` to represent indexed families of types. For example:
- Action spaces can depend on player identities
- Payoffs can depend on chosen actions
- Strategy profiles can depend on game history

### Solution Concepts

The framework supports multiple solution concepts through customizable player decision rules:
- **Nash Equilibrium**: Players maximize individual payoffs given others' strategies
- **Hicksian Equilibrium**: Players maximize social welfare (sum of utilities)
- **Subgame Perfect Equilibrium**: Using backward induction in sequential games

## File Structure

```
optics-game-theory/
├── flake.nix                    # Nix development environment
├── tesi.ipkg                    # Idris package configuration
├── README.md                    # This file
└── src/
    ├── Interfaces/
    │   └── Listable.idr        # Typeclass for enumerable types
    ├── Lenses/
    │   ├── DTypes.idr          # Dependent type definitions
    │   ├── ParaDLens.idr       # Parameterized dependent lenses
    │   ├── Operators.idr       # Categorical composition operators
    │   ├── States.idr          # State and costate abstractions
    │   └── Utils.idr           # Utility functions
    └── GameTheory/
        ├── Core.idr            # Game theory primitives
        ├── Combinators.idr     # Game construction combinators
        └── Examples/
            ├── PrisonerDilemma.idr
            ├── UltimatumGame.idr
            └── UltimatumChoice.idr
```

## How It Works: From Theory to Implementation

1. **Define your game space**: Specify action sets, payoff structures, and player types using dependent types.
2. **Construct game arenas**: Use lens operators to compose simpler game components into complex structures.
3. **Specify rationality**: Define how players make decisions (e.g., via `Argmax` for utility maximization).
4. **Compute equilibrium**: Call `Equilibrium` with your game and rationality specification to automatically compute solution concepts.

The framework automatically handles:
- Composition of player decision rules
- Propagation of payoffs through game structure
- Enumeration and filtering of rational strategy profiles

## Theoretical Foundation

This framework is built on several key insights from category theory and game theory:

- **Open Games**: Games are modeled as "open" structures that can be composed and embedded within larger contexts.
- **Lenses as Bidirectional Maps**: Lenses naturally capture the dual nature of games—forward evolution of strategies and backward propagation of payoffs.
- **Dependent Types as Game Constraints**: Type-level parameters enforce game invariants without runtime checks.

## Dependencies

- `idris2`: The dependently typed programming language
- `idris2Packages.idris2Lsp`: Language server support
- `gmp`, `libffi`, `zlib`: Runtime dependencies

## Contributing

This is a thesis project focused on demonstrating the application of dependent lenses to game theory. Contributions and extensions are welcome, particularly:
- Additional game examples and case studies
- Performance optimizations for larger games
- Documentation and tutorial improvements
- Integration with external game theory libraries

## License

MIT License – See LICENSE file for details

## Author

Matteo Rossi

## Acknowledgments

This framework builds on foundational work in **categorical game theory** and the theory of **optics** in functional programming. Special thanks to the Idris community for developing such a powerful dependently typed language, and to researchers working at the intersection of category theory and game theory for inspiration and guidance.

The parameterized lens abstraction draws from work on bidirectional transformations and category-theoretic approaches to game modeling. This project demonstrates how dependent types can bring mathematical rigor to game-theoretic modeling while maintaining practical usability.

## Further Reading

For deeper understanding of the theoretical foundations:
- Category theory and optics (lenses, prisms, etc.)
- Dependent type theory and Idris 2
- Categorical approaches to game theory and open games framework
- Bidirectional transformations and their applications

---

**Happy modeling!** 🎮📊