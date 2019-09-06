def cmovnleq1 : instruction :=
  definst "cmovnleq" $ do
    pattern fun (v_3031 : reg (bv 64)) (v_3032 : reg (bv 64)) => do
      v_4780 <- getRegister zf;
      v_4782 <- getRegister sf;
      v_4783 <- getRegister of;
      v_4786 <- getRegister v_3031;
      v_4787 <- getRegister v_3032;
      setRegister (lhs.of_reg v_3032) (mux (bit_and (notBool_ v_4780) (eq v_4782 v_4783)) v_4786 v_4787);
      pure ()
    pat_end;
    pattern fun (v_3027 : Mem) (v_3028 : reg (bv 64)) => do
      v_8101 <- getRegister zf;
      v_8103 <- getRegister sf;
      v_8104 <- getRegister of;
      v_8107 <- evaluateAddress v_3027;
      v_8108 <- load v_8107 8;
      v_8109 <- getRegister v_3028;
      setRegister (lhs.of_reg v_3028) (mux (bit_and (notBool_ v_8101) (eq v_8103 v_8104)) v_8108 v_8109);
      pure ()
    pat_end
