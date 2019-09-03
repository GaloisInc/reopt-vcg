def pcmpeqd1 : instruction :=
  definst "pcmpeqd" $ do
    pattern fun (v_3259 : reg (bv 128)) (v_3260 : reg (bv 128)) => do
      v_6903 <- getRegister v_3260;
      v_6905 <- getRegister v_3259;
      setRegister (lhs.of_reg v_3260) (concat (mux (eq (extract v_6903 0 32) (extract v_6905 0 32)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_6903 32 64) (extract v_6905 32 64)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_6903 64 96) (extract v_6905 64 96)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (eq (extract v_6903 96 128) (extract v_6905 96 128)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))));
      pure ()
    pat_end;
    pattern fun (v_3254 : Mem) (v_3255 : reg (bv 128)) => do
      v_10949 <- getRegister v_3255;
      v_10951 <- evaluateAddress v_3254;
      v_10952 <- load v_10951 16;
      setRegister (lhs.of_reg v_3255) (concat (mux (eq (extract v_10949 0 32) (extract v_10952 0 32)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_10949 32 64) (extract v_10952 32 64)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_10949 64 96) (extract v_10952 64 96)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (eq (extract v_10949 96 128) (extract v_10952 96 128)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))));
      pure ()
    pat_end
