def movw1 : instruction :=
  definst "movw" $ do
    pattern fun (v_2650 : imm int) (v_2649 : reg (bv 16)) => do
      setRegister (lhs.of_reg v_2649) (handleImmediateWithSignExtend v_2650 16 16);
      pure ()
    pat_end;
    pattern fun (v_2658 : reg (bv 16)) (v_2659 : reg (bv 16)) => do
      v_4067 <- getRegister v_2658;
      setRegister (lhs.of_reg v_2659) v_4067;
      pure ()
    pat_end;
    pattern fun (v_2642 : imm int) (v_2641 : Mem) => do
      v_8631 <- evaluateAddress v_2641;
      store v_8631 (handleImmediateWithSignExtend v_2642 16 16) 2;
      pure ()
    pat_end;
    pattern fun (v_2646 : reg (bv 16)) (v_2645 : Mem) => do
      v_8634 <- evaluateAddress v_2645;
      v_8635 <- getRegister v_2646;
      store v_8634 v_8635 2;
      pure ()
    pat_end;
    pattern fun (v_2654 : Mem) (v_2655 : reg (bv 16)) => do
      v_8871 <- evaluateAddress v_2654;
      v_8872 <- load v_8871 2;
      setRegister (lhs.of_reg v_2655) v_8872;
      pure ()
    pat_end
