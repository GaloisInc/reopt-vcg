def mulxq1 : instruction :=
  definst "mulxq" $ do
    pattern fun (v_2898 : reg (bv 64)) (v_2899 : reg (bv 64)) (v_2900 : reg (bv 64)) => do
      v_4408 <- getRegister rdx;
      v_4410 <- getRegister v_2898;
      v_4412 <- eval (mul (concat (expression.bv_nat 64 0) v_4408) (concat (expression.bv_nat 64 0) v_4410));
      setRegister (lhs.of_reg v_2899) (extract v_4412 64 128);
      setRegister (lhs.of_reg v_2900) (extract v_4412 0 64);
      pure ()
    pat_end;
    pattern fun (v_2888 : Mem) (v_2889 : reg (bv 64)) (v_2890 : reg (bv 64)) => do
      v_8947 <- evaluateAddress v_2888;
      v_8949 <- load v_8947 8;
      v_8951 <- eval (mul (concat (expression.bv_nat 64 0) v_8947) (concat (expression.bv_nat 64 0) v_8949));
      setRegister (lhs.of_reg v_2889) (extract v_8951 64 128);
      setRegister (lhs.of_reg v_2890) (extract v_8951 0 64);
      pure ()
    pat_end
