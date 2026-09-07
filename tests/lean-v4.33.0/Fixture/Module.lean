module

namespace Fixture.Module

@[expose] public def offset : Nat := 7

public theorem clean : offset = 7 := rfl
public axiom extra : offset = 7
public theorem usesExtra : offset = 7 := extra
public theorem unfinished : offset = 7 := by sorry

end Fixture.Module
