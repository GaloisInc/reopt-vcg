def xchgq1 : instruction :=
  definst "xchgq" $ do
    pattern fun (v_2686 : reg (bv 64)) (v_2687 : reg (bv 64)) => do
      v_4351 <- eval (eq (eq (convToRegKeysHelper (convSubRegsToRegs v_2686)) (convToRegKeysHelper (convSubRegsToRegs v_2687))) bit_zero);
      v_4352 <- getRegister v_2686;
      v_4353 <- getRegister v_2687;
      setRegister (lhs.of_reg v_2686) v_4353;
      setRegister (lhs.of_reg v_2687) v_4352;
      pure ()
    pat_end;
    pattern fun (v_2691 : reg (bv 64)) (v_2692 : reg (bv 64)) => do
      v_4360 <- eval (eq (convToRegKeysHelper (convSubRegsToRegs v_2691)) (convToRegKeysHelper (convSubRegsToRegs v_2692)));
      v_4361 <- getRegister v_2691;
      setRegister (lhs.of_reg v_2692) v_4361;
      pure ()
    pat_end;
    pattern fun rax (v_2696 : reg (bv 64)) => do
      v_4366 <- eval (eq (eq rax (convToRegKeysHelper (convSubRegsToRegs v_2696))) bit_zero);
      v_4367 <- getRegister v_2696;
      v_4368 <- getRegister rax;
      setRegister (lhs.of_reg v_2696) v_4368;
      setRegister rax v_4367;
      pure ()
    pat_end;
    pattern fun (v_2708 : reg (bv 64)) rax => do
      v_4386 <- eval (eq rax (convToRegKeysHelper (convSubRegsToRegs v_2708)));
      v_4387 <- getRegister rax;
      setRegister (lhs.of_reg v_2708) v_4387;
      pure ()
    pat_end;
    pattern fun (v_2678 : reg (bv 64)) (v_2677 : Mem) => do
      v_7593 <- evaluateAddress v_2677;
      v_7594 <- getRegister v_2678;
      store v_7593 v_7594 8;
      setRegister (lhs.of_reg v_2678) v_7596;
      pure ()
    pat_end;
    pattern fun (v_2681 : Mem) (v_2682 : reg (bv 64)) => do
      v_7598 <- evaluateAddress v_2681;
      v_7599 <- getRegister v_2682;
      store v_7598 v_7599 8;
      setRegister (lhs.of_reg v_2682) v_7601;
      pure ()
    pat_end
