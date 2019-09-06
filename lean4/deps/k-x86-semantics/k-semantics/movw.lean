def movw1 : instruction :=
  definst "movw" $ do
    pattern fun (v_2725 : imm int) (v_2726 : reg (bv 16)) => do
      setRegister (lhs.of_reg v_2726) (handleImmediateWithSignExtend v_2725 16 16);
      pure ()
    pat_end;
    pattern fun (v_2734 : reg (bv 16)) (v_2735 : reg (bv 16)) => do
      v_4145 <- getRegister v_2734;
      setRegister (lhs.of_reg v_2735) v_4145;
      pure ()
    pat_end;
    pattern fun (v_2718 : imm int) (v_2717 : Mem) => do
      v_8522 <- evaluateAddress v_2717;
      store v_8522 (handleImmediateWithSignExtend v_2718 16 16) 2;
      pure ()
    pat_end;
    pattern fun (v_2722 : reg (bv 16)) (v_2721 : Mem) => do
      v_8525 <- evaluateAddress v_2721;
      v_8526 <- getRegister v_2722;
      store v_8525 v_8526 2;
      pure ()
    pat_end;
    pattern fun (v_2730 : Mem) (v_2731 : reg (bv 16)) => do
      v_8762 <- evaluateAddress v_2730;
      v_8763 <- load v_8762 2;
      setRegister (lhs.of_reg v_2731) v_8763;
      pure ()
    pat_end
