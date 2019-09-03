def movmskpd1 : instruction :=
  definst "movmskpd" $ do
    pattern fun (v_2514 : reg (bv 128)) (v_2515 : reg (bv 32)) => do
      v_3930 <- getRegister v_2514;
      setRegister (lhs.of_reg v_2515) (concat (expression.bv_nat 30 0) (concat (extract v_3930 0 1) (extract v_3930 64 65)));
      pure ()
    pat_end;
    pattern fun (v_2519 : reg (bv 128)) (v_2520 : reg (bv 64)) => do
      v_3936 <- getRegister v_2519;
      setRegister (lhs.of_reg v_2520) (concat (expression.bv_nat 62 0) (concat (extract v_3936 0 1) (extract v_3936 64 65)));
      pure ()
    pat_end
