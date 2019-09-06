def movd1 : instruction :=
  definst "movd" $ do
    pattern fun (v_2489 : reg (bv 128)) (v_2490 : reg (bv 32)) => do
      v_3923 <- getRegister v_2489;
      setRegister (lhs.of_reg v_2490) (extract v_3923 96 128);
      pure ()
    pat_end;
    pattern fun (v_2499 : reg (bv 32)) (v_2498 : reg (bv 128)) => do
      v_3930 <- getRegister v_2499;
      setRegister (lhs.of_reg v_2498) (concat (expression.bv_nat 96 0) v_3930);
      pure ()
    pat_end;
    pattern fun (v_2486 : reg (bv 128)) (v_2485 : Mem) => do
      v_8444 <- evaluateAddress v_2485;
      v_8445 <- getRegister v_2486;
      store v_8444 (extract v_8445 96 128) 4;
      pure ()
    pat_end;
    pattern fun (v_2494 : Mem) (v_2495 : reg (bv 128)) => do
      v_8705 <- evaluateAddress v_2494;
      v_8706 <- load v_8705 4;
      setRegister (lhs.of_reg v_2495) (concat (expression.bv_nat 96 0) v_8706);
      pure ()
    pat_end
