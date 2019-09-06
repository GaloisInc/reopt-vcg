def andnpd1 : instruction :=
  definst "andnpd" $ do
    pattern fun (v_2882 : reg (bv 128)) (v_2883 : reg (bv 128)) => do
      v_5257 <- getRegister v_2883;
      v_5259 <- getRegister v_2882;
      setRegister (lhs.of_reg v_2883) (bv_and (bv_xor v_5257 (expression.bv_nat 128 340282366920938463463374607431768211455)) v_5259);
      pure ()
    pat_end;
    pattern fun (v_2881 : Mem) (v_2878 : reg (bv 128)) => do
      v_8990 <- getRegister v_2878;
      v_8992 <- evaluateAddress v_2881;
      v_8993 <- load v_8992 16;
      setRegister (lhs.of_reg v_2878) (bv_and (bv_xor v_8990 (expression.bv_nat 128 340282366920938463463374607431768211455)) v_8993);
      pure ()
    pat_end
