def cmovnbel1 : instruction :=
  definst "cmovnbel" $ do
    pattern fun (v_2863 : reg (bv 32)) (v_2864 : reg (bv 32)) => do
      v_4559 <- getRegister cf;
      v_4561 <- getRegister zf;
      v_4564 <- getRegister v_2863;
      v_4565 <- getRegister v_2864;
      setRegister (lhs.of_reg v_2864) (mux (bit_and (notBool_ v_4559) (notBool_ v_4561)) v_4564 v_4565);
      pure ()
    pat_end;
    pattern fun (v_2856 : Mem) (v_2859 : reg (bv 32)) => do
      v_7937 <- getRegister cf;
      v_7939 <- getRegister zf;
      v_7942 <- evaluateAddress v_2856;
      v_7943 <- load v_7942 4;
      v_7944 <- getRegister v_2859;
      setRegister (lhs.of_reg v_2859) (mux (bit_and (notBool_ v_7937) (notBool_ v_7939)) v_7943 v_7944);
      pure ()
    pat_end
