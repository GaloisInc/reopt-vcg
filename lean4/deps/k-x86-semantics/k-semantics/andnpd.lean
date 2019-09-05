def andnpd1 : instruction :=
  definst "andnpd" $ do
    pattern fun (v_2858 : reg (bv 128)) (v_2859 : reg (bv 128)) => do
      v_5376 <- getRegister v_2859;
      v_5378 <- getRegister v_2858;
      setRegister (lhs.of_reg v_2859) (bv_and (bv_xor v_5376 (expression.bv_nat 128 340282366920938463463374607431768211455)) v_5378);
      pure ()
    pat_end;
    pattern fun (v_2853 : Mem) (v_2854 : reg (bv 128)) => do
      v_9166 <- getRegister v_2854;
      v_9168 <- evaluateAddress v_2853;
      v_9169 <- load v_9168 16;
      setRegister (lhs.of_reg v_2854) (bv_and (bv_xor v_9166 (expression.bv_nat 128 340282366920938463463374607431768211455)) v_9169);
      pure ()
    pat_end
