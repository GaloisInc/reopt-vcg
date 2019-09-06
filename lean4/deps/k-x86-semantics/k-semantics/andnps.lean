def andnps1 : instruction :=
  definst "andnps" $ do
    pattern fun (v_2891 : reg (bv 128)) (v_2892 : reg (bv 128)) => do
      v_5266 <- getRegister v_2892;
      v_5268 <- getRegister v_2891;
      setRegister (lhs.of_reg v_2892) (bv_and (bv_xor v_5266 (expression.bv_nat 128 340282366920938463463374607431768211455)) v_5268);
      pure ()
    pat_end;
    pattern fun (v_2890 : Mem) (v_2887 : reg (bv 128)) => do
      v_8996 <- getRegister v_2887;
      v_8998 <- evaluateAddress v_2890;
      v_8999 <- load v_8998 16;
      setRegister (lhs.of_reg v_2887) (bv_and (bv_xor v_8996 (expression.bv_nat 128 340282366920938463463374607431768211455)) v_8999);
      pure ()
    pat_end
