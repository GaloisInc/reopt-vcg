def cmovlq1 : instruction :=
  definst "cmovlq" $ do
    pattern fun (v_2788 : reg (bv 64)) (v_2789 : reg (bv 64)) => do
      v_4475 <- getRegister sf;
      v_4476 <- getRegister of;
      v_4479 <- getRegister v_2788;
      v_4480 <- getRegister v_2789;
      setRegister (lhs.of_reg v_2789) (mux (notBool_ (eq v_4475 v_4476)) v_4479 v_4480);
      pure ()
    pat_end;
    pattern fun (v_2784 : Mem) (v_2785 : reg (bv 64)) => do
      v_7877 <- getRegister sf;
      v_7878 <- getRegister of;
      v_7881 <- evaluateAddress v_2784;
      v_7882 <- load v_7881 8;
      v_7883 <- getRegister v_2785;
      setRegister (lhs.of_reg v_2785) (mux (notBool_ (eq v_7877 v_7878)) v_7882 v_7883);
      pure ()
    pat_end
