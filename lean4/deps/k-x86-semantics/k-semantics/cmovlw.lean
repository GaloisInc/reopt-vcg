def cmovlw1 : instruction :=
  definst "cmovlw" $ do
    pattern fun (v_2797 : reg (bv 16)) (v_2798 : reg (bv 16)) => do
      v_4487 <- getRegister sf;
      v_4488 <- getRegister of;
      v_4491 <- getRegister v_2797;
      v_4492 <- getRegister v_2798;
      setRegister (lhs.of_reg v_2798) (mux (notBool_ (eq v_4487 v_4488)) v_4491 v_4492);
      pure ()
    pat_end;
    pattern fun (v_2793 : Mem) (v_2794 : reg (bv 16)) => do
      v_7886 <- getRegister sf;
      v_7887 <- getRegister of;
      v_7890 <- evaluateAddress v_2793;
      v_7891 <- load v_7890 2;
      v_7892 <- getRegister v_2794;
      setRegister (lhs.of_reg v_2794) (mux (notBool_ (eq v_7886 v_7887)) v_7891 v_7892);
      pure ()
    pat_end
