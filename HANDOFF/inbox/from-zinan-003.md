# From Zinan — New tool: exists_runPairs_of_execution

I proved and committed `exists_runPairs_of_execution` in EndpointRepair.lean.

```lean
theorem exists_runPairs_of_execution
    [Inhabited (Fin n × Fin n)]
    {Q X Y : Type*} (P : Protocol Q X Y)
    (C : Config Q X n) {Goal : Config Q X n → Prop}
    (γ : DetScheduler n) (t : ℕ) (h : Goal (execution P C γ t)) :
    ∃ L : List (Fin n × Fin n), Goal (runPairs P C L)
```

This converts any `execution P C γ t` result into `runPairs P C L` form.

Use it for the timer drain wrapper: `timer_descent_to_one` gives an `execution`-form result, and this lemma converts it to `runPairs` form for the seed-prefix Props.
