def movd1 : instruction :=
  definst "movd" $ do
    pattern fun (v_2401 : reg (bv 128)) (v_2402 : reg (bv 32)) => do
      v_3832 <- getRegister v_2401;
      setRegister (lhs.of_reg v_2402) (extract v_3832 96 128);
      pure ()
    pat_end;
    pattern fun (v_2411 : reg (bv 32)) (v_2410 : reg (bv 128)) => do
      v_3839 <- getRegister v_2411;
      setRegister (lhs.of_reg v_2410) (concat (expression.bv_nat 96 0) v_3839);
      pure ()
    pat_end;
    pattern fun (v_2397 : reg (bv 128)) (v_2396 : Mem) => do
      v_8573 <- evaluateAddress v_2396;
      v_8574 <- getRegister v_2397;
      store v_8573 (extract v_8574 96 128) 4;
      pure ()
    pat_end;
    pattern fun (v_2405 : Mem) (v_2406 : reg (bv 128)) => do
      v_8835 <- evaluateAddress v_2405;
      v_8836 <- load v_8835 4;
      setRegister (lhs.of_reg v_2406) (concat (expression.bv_nat 96 0) v_8836);
      pure ()
    pat_end
