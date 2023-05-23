# Defining Pos category

Challenges:  
- type of objects  
- type of morphisms

Objects of the category should be preorders. But if we define preorder as a type class taking the type of the set as a parameter, then how do we express the object type?

We can have `obj := poset Type*`, but then defining morphism as `hom := λ X Y, {f : X → Y // ∀ x y, x ≤ y → f x ≤ f y}` fails, since “`type expected at X, term has type preorder (Type ?)`” (which from what I understand means that `X` is a term, not a type, so we would have to coerce the type of the poset term out). Not sure how to do that with this version of the code.

So then we have to include the actual type of the poset, not just the proof of it being a poset, within the `obj` type. Having something like a Pi-type for `obj` implies that all types also have a proof for poset, not true. Sigma-type maybe? Then an object is a pair of its type and the proof of the type being a poset, which could (does!) work. Check out branch [define-poset-sigma](https://gitlab.ewi.tudelft.nl/bpahrens/ct/-/tree/define-poset-sigma) for this definition.

Another method of doing this would be embedding the type and the operation inside the type class. Check out branch [def-poset-bundle](https://gitlab.ewi.tudelft.nl/bpahrens/ct/-/tree/define-poset-bundle) for this definition. This also cleans up the poset category, with `obj` becoming just `poset`, and stuff like morphism definition becoming clearer to read (once the coercion from poset to type is added).

However, it still has some problems, mainly the Lean info view not displaying the context properly (`preorder.le`  hiding the actual poset in the morphism, although internally it does depend on the poset), but it can still be made to work with identical proofs.

We would ideally want to have the accurate goal context from the Σ-definition, with the definition clarity of the bundled definition. If we take a look at the Σ definition for the morphisms, the problem comes from the `obj` type simply bundling the type and proof without any other properties.

We can simply create a new type class, `poset_universe`, which bundles together the type of the poset with the proof of poset. On this new type we can add a coercion to type similarly to the bundle definition, so that `X : poset` with type `α` can be interpreted as just the type `↑X` equivalent to `α`, and defining a `has_le` instance so that when we have `x y : ↑X`, `x ≤ y` becomes equivalent to `X.proof.le x y`. See commit [de457c77](https://gitlab.ewi.tudelft.nl/bpahrens/ct/-/commit/de457c77f29b8ce41aff226480f2b83091e54a2b) for this version.