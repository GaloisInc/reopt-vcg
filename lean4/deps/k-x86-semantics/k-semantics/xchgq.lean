def xchgq1 : instruction :=
  definst "xchgq" $ do
    pattern fun (v_2685 : reg (bv 64)) (v_2686 : reg (bv 64)) => do
      v_4351 <- eval (eq (eq (convToRegKeysHelper (convSubRegsToRegs v_2685)) (convToRegKeysHelper (convSubRegsToRegs v_2686))) bit_zero);
      v_4352 <- getRegister v_2686;
      v_4353 <- getRegister v_2685;
      setRegister (lhs.of_reg v_2686) v_4353;
      setRegister (lhs.of_reg v_2685) v_4352;
      pure ()
    pat_end;
    pattern fun (v_2690 : reg (bv 64)) (v_2691 : reg (bv 64)) => do
      v_4360 <- eval (eq (convToRegKeysHelper (convSubRegsToRegs v_2690)) (convToRegKeysHelper (convSubRegsToRegs v_2691)));
      v_4361 <- getRegister v_2690;
      setRegister (lhs.of_reg v_2691) v_4361;
      pure ()
    pat_end;
    pattern fun (v_2703 : reg (bv 64)) rax => do
      v_4379 <- eval (eq (eq rax (convToRegKeysHelper (convSubRegsToRegs v_2703))) bit_zero);
      v_4380 <- getRegister v_2703;
      v_4381 <- getRegister rax;
      setRegister (lhs.of_reg v_2703) v_4381;
      setRegister rax v_4380;
      pure ()
    pat_end;
    pattern fun (v_2707 : reg (bv 64)) rax => do
      v_4386 <- eval (eq rax (convToRegKeysHelper (convSubRegsToRegs v_2707)));
      v_4387 <- getRegister rax;
      setRegister (lhs.of_reg v_2707) v_4387;
      pure ()
    pat_end;
    pattern fun (v_2677 : reg (bv 64)) (v_2678 : Mem) => do
      v_7593 <- evaluateAddress v_2678;
      v_7594 <- getRegister v_2677;
      store v_7593 v_7594 8;
      setRegister (lhs.of_reg v_2677) v_7596;
      pure ()
    pat_end;
    pattern fun (v_2682 : Mem) (v_2681 : reg (bv 64)) => do
      v_7598 <- evaluateAddress v_2682;
      v_7599 <- getRegister v_2681;
      store v_7598 v_7599 8;
      setRegister (lhs.of_reg v_2681) v_7601;
      pure ()
    pat_end
