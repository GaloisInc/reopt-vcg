def vpmuludq1 : instruction :=
  definst "vpmuludq" $ do
    pattern fun (v_3005 : reg (bv 128)) (v_3006 : reg (bv 128)) (v_3007 : reg (bv 128)) => do
      v_6909 <- getRegister v_3006;
      v_6912 <- getRegister v_3005;
      setRegister (lhs.of_reg v_3007) (concat (mul (concat (expression.bv_nat 32 0) (extract v_6909 32 64)) (concat (expression.bv_nat 32 0) (extract v_6912 32 64))) (mul (concat (expression.bv_nat 32 0) (extract v_6909 96 128)) (concat (expression.bv_nat 32 0) (extract v_6912 96 128))));
      pure ()
    pat_end;
    pattern fun (v_3016 : reg (bv 256)) (v_3017 : reg (bv 256)) (v_3018 : reg (bv 256)) => do
      v_6928 <- getRegister v_3017;
      v_6931 <- getRegister v_3016;
      setRegister (lhs.of_reg v_3018) (concat (mul (concat (expression.bv_nat 32 0) (extract v_6928 32 64)) (concat (expression.bv_nat 32 0) (extract v_6931 32 64))) (concat (mul (concat (expression.bv_nat 32 0) (extract v_6928 96 128)) (concat (expression.bv_nat 32 0) (extract v_6931 96 128))) (concat (mul (concat (expression.bv_nat 32 0) (extract v_6928 160 192)) (concat (expression.bv_nat 32 0) (extract v_6931 160 192))) (mul (concat (expression.bv_nat 32 0) (extract v_6928 224 256)) (concat (expression.bv_nat 32 0) (extract v_6931 224 256))))));
      pure ()
    pat_end;
    pattern fun (v_2999 : Mem) (v_3000 : reg (bv 128)) (v_3001 : reg (bv 128)) => do
      v_13219 <- getRegister v_3000;
      v_13222 <- evaluateAddress v_2999;
      v_13223 <- load v_13222 16;
      setRegister (lhs.of_reg v_3001) (concat (mul (concat (expression.bv_nat 32 0) (extract v_13219 32 64)) (concat (expression.bv_nat 32 0) (extract v_13223 32 64))) (mul (concat (expression.bv_nat 32 0) (extract v_13219 96 128)) (concat (expression.bv_nat 32 0) (extract v_13223 96 128))));
      pure ()
    pat_end;
    pattern fun (v_3010 : Mem) (v_3011 : reg (bv 256)) (v_3012 : reg (bv 256)) => do
      v_13234 <- getRegister v_3011;
      v_13237 <- evaluateAddress v_3010;
      v_13238 <- load v_13237 32;
      setRegister (lhs.of_reg v_3012) (concat (mul (concat (expression.bv_nat 32 0) (extract v_13234 32 64)) (concat (expression.bv_nat 32 0) (extract v_13238 32 64))) (concat (mul (concat (expression.bv_nat 32 0) (extract v_13234 96 128)) (concat (expression.bv_nat 32 0) (extract v_13238 96 128))) (concat (mul (concat (expression.bv_nat 32 0) (extract v_13234 160 192)) (concat (expression.bv_nat 32 0) (extract v_13238 160 192))) (mul (concat (expression.bv_nat 32 0) (extract v_13234 224 256)) (concat (expression.bv_nat 32 0) (extract v_13238 224 256))))));
      pure ()
    pat_end
