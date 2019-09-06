def cmovns1 : instruction :=
  definst "cmovns" $ do
    pattern fun (v_3126 : Mem) (v_3129 : reg (bv 32)) => do
      v_8732 <- getRegister sf;
      v_8734 <- evaluateAddress v_3126;
      v_8735 <- load v_8734 4;
      v_8736 <- getRegister v_3129;
      setRegister (lhs.of_reg v_3129) (mux (notBool_ v_8732) v_8735 v_8736);
      pure ()
    pat_end;
    pattern fun (v_3144 : Mem) (v_3143 : reg (bv 64)) => do
      v_8739 <- getRegister sf;
      v_8741 <- evaluateAddress v_3144;
      v_8742 <- load v_8741 8;
      v_8743 <- getRegister v_3143;
      setRegister (lhs.of_reg v_3143) (mux (notBool_ v_8739) v_8742 v_8743);
      pure ()
    pat_end;
    pattern fun (v_3160 : Mem) (v_3161 : reg (bv 16)) => do
      v_8746 <- getRegister sf;
      v_8748 <- evaluateAddress v_3160;
      v_8749 <- load v_8748 2;
      v_8750 <- getRegister v_3161;
      setRegister (lhs.of_reg v_3161) (mux (notBool_ v_8746) v_8749 v_8750);
      pure ()
    pat_end
