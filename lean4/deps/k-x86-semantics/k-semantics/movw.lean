def movw1 : instruction :=
  definst "movw" $ do
    pattern fun (v_2637 : imm int) (v_2638 : reg (bv 16)) => do
      setRegister (lhs.of_reg v_2638) (handleImmediateWithSignExtend v_2637 16 16);
      pure ()
    pat_end;
    pattern fun (v_2646 : reg (bv 16)) (v_2647 : reg (bv 16)) => do
      v_4054 <- getRegister v_2646;
      setRegister (lhs.of_reg v_2647) v_4054;
      pure ()
    pat_end;
    pattern fun (v_2629 : imm int) (v_2628 : Mem) => do
      v_8652 <- evaluateAddress v_2628;
      store v_8652 (handleImmediateWithSignExtend v_2629 16 16) 2;
      pure ()
    pat_end;
    pattern fun (v_2633 : reg (bv 16)) (v_2632 : Mem) => do
      v_8655 <- evaluateAddress v_2632;
      v_8656 <- getRegister v_2633;
      store v_8655 v_8656 2;
      pure ()
    pat_end;
    pattern fun (v_2641 : Mem) (v_2642 : reg (bv 16)) => do
      v_8892 <- evaluateAddress v_2641;
      v_8893 <- load v_8892 2;
      setRegister (lhs.of_reg v_2642) v_8893;
      pure ()
    pat_end
