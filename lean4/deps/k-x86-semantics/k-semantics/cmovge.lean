def cmovge1 : instruction :=
  definst "cmovge" $ do
    pattern fun (v_2646 : Mem) (v_2649 : reg (bv 32)) => do
      v_8675 <- getRegister sf;
      v_8676 <- getRegister of;
      v_8678 <- evaluateAddress v_2646;
      v_8679 <- load v_8678 4;
      v_8680 <- getRegister v_2649;
      setRegister (lhs.of_reg v_2649) (mux (eq v_8675 v_8676) v_8679 v_8680);
      pure ()
    pat_end;
    pattern fun (v_2664 : Mem) (v_2663 : reg (bv 64)) => do
      v_8683 <- getRegister sf;
      v_8684 <- getRegister of;
      v_8686 <- evaluateAddress v_2664;
      v_8687 <- load v_8686 8;
      v_8688 <- getRegister v_2663;
      setRegister (lhs.of_reg v_2663) (mux (eq v_8683 v_8684) v_8687 v_8688);
      pure ()
    pat_end;
    pattern fun (v_2680 : Mem) (v_2681 : reg (bv 16)) => do
      v_8691 <- getRegister sf;
      v_8692 <- getRegister of;
      v_8694 <- evaluateAddress v_2680;
      v_8695 <- load v_8694 2;
      v_8696 <- getRegister v_2681;
      setRegister (lhs.of_reg v_2681) (mux (eq v_8691 v_8692) v_8695 v_8696);
      pure ()
    pat_end
