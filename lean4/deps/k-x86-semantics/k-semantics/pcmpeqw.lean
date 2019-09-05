def pcmpeqw1 : instruction :=
  definst "pcmpeqw" $ do
    pattern fun (v_2446 : reg (bv 128)) (v_2447 : reg (bv 128)) => do
      v_3873 <- getRegister v_2447;
      v_3875 <- getRegister v_2446;
      setRegister (lhs.of_reg v_2447) (concat (mux (eq (extract v_3873 0 16) (extract v_3875 0 16)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (eq (extract v_3873 16 32) (extract v_3875 16 32)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (eq (extract v_3873 32 48) (extract v_3875 32 48)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (eq (extract v_3873 48 64) (extract v_3875 48 64)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (eq (extract v_3873 64 80) (extract v_3875 64 80)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (eq (extract v_3873 80 96) (extract v_3875 80 96)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (eq (extract v_3873 96 112) (extract v_3875 96 112)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (mux (eq (extract v_3873 112 128) (extract v_3875 112 128)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)))))))));
      pure ()
    pat_end;
    pattern fun (v_2443 : Mem) (v_2442 : reg (bv 128)) => do
      v_10848 <- getRegister v_2442;
      v_10850 <- evaluateAddress v_2443;
      v_10851 <- load v_10850 16;
      setRegister (lhs.of_reg v_2442) (concat (mux (eq (extract v_10848 0 16) (extract v_10851 0 16)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (eq (extract v_10848 16 32) (extract v_10851 16 32)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (eq (extract v_10848 32 48) (extract v_10851 32 48)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (eq (extract v_10848 48 64) (extract v_10851 48 64)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (eq (extract v_10848 64 80) (extract v_10851 64 80)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (eq (extract v_10848 80 96) (extract v_10851 80 96)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (eq (extract v_10848 96 112) (extract v_10851 96 112)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (mux (eq (extract v_10848 112 128) (extract v_10851 112 128)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)))))))));
      pure ()
    pat_end
