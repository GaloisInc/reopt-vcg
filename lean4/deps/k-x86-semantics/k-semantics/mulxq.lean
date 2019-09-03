def mulxq1 : instruction :=
  definst "mulxq" $ do
    pattern fun (v_2810 : reg (bv 64)) (v_2811 : reg (bv 64)) (v_2812 : reg (bv 64)) => do
      v_4322 <- getRegister rdx;
      v_4324 <- getRegister v_2810;
      v_4326 <- eval (mul (concat (expression.bv_nat 64 0) v_4322) (concat (expression.bv_nat 64 0) v_4324));
      setRegister (lhs.of_reg v_2812) (extract v_4326 0 64);
      setRegister (lhs.of_reg v_2811) (extract v_4326 64 128);
      pure ()
    pat_end;
    pattern fun (v_2799 : Mem) (v_2800 : reg (bv 64)) (v_2801 : reg (bv 64)) => do
      v_9081 <- evaluateAddress v_2799;
      v_9083 <- load v_9081 8;
      v_9085 <- eval (mul (concat (expression.bv_nat 64 0) v_9081) (concat (expression.bv_nat 64 0) v_9083));
      setRegister (lhs.of_reg v_2800) (extract v_9085 64 128);
      setRegister (lhs.of_reg v_2801) (extract v_9085 0 64);
      pure ()
    pat_end
