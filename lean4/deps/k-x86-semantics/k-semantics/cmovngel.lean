def cmovngel1 : instruction :=
  definst "cmovngel" $ do
    pattern fun (v_2971 : reg (bv 32)) (v_2972 : reg (bv 32)) => do
      v_4688 <- getRegister sf;
      v_4689 <- getRegister of;
      v_4692 <- getRegister v_2971;
      v_4693 <- getRegister v_2972;
      setRegister (lhs.of_reg v_2972) (mux (notBool_ (eq v_4688 v_4689)) v_4692 v_4693);
      pure ()
    pat_end;
    pattern fun (v_2964 : Mem) (v_2967 : reg (bv 32)) => do
      v_8030 <- getRegister sf;
      v_8031 <- getRegister of;
      v_8034 <- evaluateAddress v_2964;
      v_8035 <- load v_8034 4;
      v_8036 <- getRegister v_2967;
      setRegister (lhs.of_reg v_2967) (mux (notBool_ (eq v_8030 v_8031)) v_8035 v_8036);
      pure ()
    pat_end
