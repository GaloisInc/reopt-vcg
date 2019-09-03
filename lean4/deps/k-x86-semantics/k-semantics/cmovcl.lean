def cmovcl1 : instruction :=
  definst "cmovcl" $ do
    pattern fun (v_2518 : reg (bv 32)) (v_2519 : reg (bv 32)) => do
      v_4201 <- getRegister cf;
      v_4203 <- getRegister v_2518;
      v_4204 <- getRegister v_2519;
      setRegister (lhs.of_reg v_2519) (mux (eq v_4201 (expression.bv_nat 1 1)) v_4203 v_4204);
      pure ()
    pat_end;
    pattern fun (v_2514 : Mem) (v_2515 : reg (bv 32)) => do
      v_7887 <- getRegister cf;
      v_7889 <- evaluateAddress v_2514;
      v_7890 <- load v_7889 4;
      v_7891 <- getRegister v_2515;
      setRegister (lhs.of_reg v_2515) (mux (eq v_7887 (expression.bv_nat 1 1)) v_7890 v_7891);
      pure ()
    pat_end
