def vblendvps1 : instruction :=
  definst "vblendvps" $ do
    pattern fun (v_2860 : reg (bv 128)) (v_2861 : reg (bv 128)) (v_2862 : reg (bv 128)) (v_2863 : reg (bv 128)) => do
      v_5895 <- getRegister v_2860;
      v_5898 <- getRegister v_2862;
      v_5900 <- getRegister v_2861;
      setRegister (lhs.of_reg v_2863) (concat (mux (eq (extract v_5895 0 1) (expression.bv_nat 1 0)) (extract v_5898 0 32) (extract v_5900 0 32)) (concat (mux (eq (extract v_5895 32 33) (expression.bv_nat 1 0)) (extract v_5898 32 64) (extract v_5900 32 64)) (concat (mux (eq (extract v_5895 64 65) (expression.bv_nat 1 0)) (extract v_5898 64 96) (extract v_5900 64 96)) (mux (eq (extract v_5895 96 97) (expression.bv_nat 1 0)) (extract v_5898 96 128) (extract v_5900 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_2870 : reg (bv 256)) (v_2871 : reg (bv 256)) (v_2872 : reg (bv 256)) (v_2873 : reg (bv 256)) => do
      v_5928 <- getRegister v_2870;
      v_5931 <- getRegister v_2872;
      v_5933 <- getRegister v_2871;
      setRegister (lhs.of_reg v_2873) (concat (mux (eq (extract v_5928 0 1) (expression.bv_nat 1 0)) (extract v_5931 0 32) (extract v_5933 0 32)) (concat (mux (eq (extract v_5928 32 33) (expression.bv_nat 1 0)) (extract v_5931 32 64) (extract v_5933 32 64)) (concat (mux (eq (extract v_5928 64 65) (expression.bv_nat 1 0)) (extract v_5931 64 96) (extract v_5933 64 96)) (concat (mux (eq (extract v_5928 96 97) (expression.bv_nat 1 0)) (extract v_5931 96 128) (extract v_5933 96 128)) (concat (mux (eq (extract v_5928 128 129) (expression.bv_nat 1 0)) (extract v_5931 128 160) (extract v_5933 128 160)) (concat (mux (eq (extract v_5928 160 161) (expression.bv_nat 1 0)) (extract v_5931 160 192) (extract v_5933 160 192)) (concat (mux (eq (extract v_5928 192 193) (expression.bv_nat 1 0)) (extract v_5931 192 224) (extract v_5933 192 224)) (mux (eq (extract v_5928 224 225) (expression.bv_nat 1 0)) (extract v_5931 224 256) (extract v_5933 224 256)))))))));
      pure ()
    pat_end;
    pattern fun (v_2854 : reg (bv 128)) (v_2851 : Mem) (v_2855 : reg (bv 128)) (v_2856 : reg (bv 128)) => do
      v_11342 <- getRegister v_2854;
      v_11345 <- getRegister v_2855;
      v_11347 <- evaluateAddress v_2851;
      v_11348 <- load v_11347 16;
      setRegister (lhs.of_reg v_2856) (concat (mux (eq (extract v_11342 0 1) (expression.bv_nat 1 0)) (extract v_11345 0 32) (extract v_11348 0 32)) (concat (mux (eq (extract v_11342 32 33) (expression.bv_nat 1 0)) (extract v_11345 32 64) (extract v_11348 32 64)) (concat (mux (eq (extract v_11342 64 65) (expression.bv_nat 1 0)) (extract v_11345 64 96) (extract v_11348 64 96)) (mux (eq (extract v_11342 96 97) (expression.bv_nat 1 0)) (extract v_11345 96 128) (extract v_11348 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_2865 : reg (bv 256)) (v_2864 : Mem) (v_2866 : reg (bv 256)) (v_2867 : reg (bv 256)) => do
      v_11370 <- getRegister v_2865;
      v_11373 <- getRegister v_2866;
      v_11375 <- evaluateAddress v_2864;
      v_11376 <- load v_11375 32;
      setRegister (lhs.of_reg v_2867) (concat (mux (eq (extract v_11370 0 1) (expression.bv_nat 1 0)) (extract v_11373 0 32) (extract v_11376 0 32)) (concat (mux (eq (extract v_11370 32 33) (expression.bv_nat 1 0)) (extract v_11373 32 64) (extract v_11376 32 64)) (concat (mux (eq (extract v_11370 64 65) (expression.bv_nat 1 0)) (extract v_11373 64 96) (extract v_11376 64 96)) (concat (mux (eq (extract v_11370 96 97) (expression.bv_nat 1 0)) (extract v_11373 96 128) (extract v_11376 96 128)) (concat (mux (eq (extract v_11370 128 129) (expression.bv_nat 1 0)) (extract v_11373 128 160) (extract v_11376 128 160)) (concat (mux (eq (extract v_11370 160 161) (expression.bv_nat 1 0)) (extract v_11373 160 192) (extract v_11376 160 192)) (concat (mux (eq (extract v_11370 192 193) (expression.bv_nat 1 0)) (extract v_11373 192 224) (extract v_11376 192 224)) (mux (eq (extract v_11370 224 225) (expression.bv_nat 1 0)) (extract v_11373 224 256) (extract v_11376 224 256)))))))));
      pure ()
    pat_end
