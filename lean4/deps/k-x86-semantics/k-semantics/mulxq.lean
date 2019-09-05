def mulxq1 : instruction :=
  definst "mulxq" $ do
    pattern fun (v_2872 : reg (bv 64)) (v_2873 : reg (bv 64)) (v_2874 : reg (bv 64)) => do
      v_4381 <- getRegister rdx;
      v_4383 <- getRegister v_2872;
      v_4385 <- eval (mul (concat (expression.bv_nat 64 0) v_4381) (concat (expression.bv_nat 64 0) v_4383));
      setRegister (lhs.of_reg v_2874) (extract v_4385 0 64);
      setRegister (lhs.of_reg v_2873) (extract v_4385 64 128);
      pure ()
    pat_end;
    pattern fun (v_2862 : Mem) (v_2863 : reg (bv 64)) (v_2864 : reg (bv 64)) => do
      v_8920 <- evaluateAddress v_2862;
      v_8922 <- load v_8920 8;
      v_8924 <- eval (mul (concat (expression.bv_nat 64 0) v_8920) (concat (expression.bv_nat 64 0) v_8922));
      setRegister (lhs.of_reg v_2863) (extract v_8924 64 128);
      setRegister (lhs.of_reg v_2864) (extract v_8924 0 64);
      pure ()
    pat_end
