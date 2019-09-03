def vshufps1 : instruction :=
  definst "vshufps" $ do
    pattern fun (v_2943 : imm int) (v_2944 : reg (bv 128)) (v_2945 : reg (bv 128)) (v_2946 : reg (bv 128)) => do
      v_6934 <- eval (handleImmediateWithSignExtend v_2943 8 8);
      v_6938 <- eval (eq (extract v_6934 0 1) (expression.bv_nat 1 1));
      v_6939 <- getRegister v_2944;
      v_6940 <- eval (extract v_6939 0 32);
      v_6941 <- eval (extract v_6939 64 96);
      v_6943 <- eval (extract v_6939 32 64);
      v_6944 <- eval (extract v_6939 96 128);
      v_6950 <- eval (eq (extract v_6934 2 3) (expression.bv_nat 1 1));
      v_6957 <- eval (eq (extract v_6934 4 5) (expression.bv_nat 1 1));
      v_6958 <- getRegister v_2945;
      v_6959 <- eval (extract v_6958 0 32);
      v_6960 <- eval (extract v_6958 64 96);
      v_6962 <- eval (extract v_6958 32 64);
      v_6963 <- eval (extract v_6958 96 128);
      v_6969 <- eval (eq (extract v_6934 6 7) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_2946) (concat (mux (eq (extract v_6934 1 2) (expression.bv_nat 1 1)) (mux v_6938 v_6940 v_6941) (mux v_6938 v_6943 v_6944)) (concat (mux (eq (extract v_6934 3 4) (expression.bv_nat 1 1)) (mux v_6950 v_6940 v_6941) (mux v_6950 v_6943 v_6944)) (concat (mux (eq (extract v_6934 5 6) (expression.bv_nat 1 1)) (mux v_6957 v_6959 v_6960) (mux v_6957 v_6962 v_6963)) (mux (eq (extract v_6934 7 8) (expression.bv_nat 1 1)) (mux v_6969 v_6959 v_6960) (mux v_6969 v_6962 v_6963)))));
      pure ()
    pat_end;
    pattern fun (v_2956 : imm int) (v_2957 : reg (bv 256)) (v_2958 : reg (bv 256)) (v_2959 : reg (bv 256)) => do
      v_6983 <- eval (handleImmediateWithSignExtend v_2956 8 8);
      v_6985 <- eval (eq (extract v_6983 1 2) (expression.bv_nat 1 1));
      v_6987 <- eval (eq (extract v_6983 0 1) (expression.bv_nat 1 1));
      v_6988 <- getRegister v_2957;
      v_6989 <- eval (extract v_6988 0 32);
      v_6990 <- eval (extract v_6988 64 96);
      v_6992 <- eval (extract v_6988 32 64);
      v_6993 <- eval (extract v_6988 96 128);
      v_6997 <- eval (eq (extract v_6983 3 4) (expression.bv_nat 1 1));
      v_6999 <- eval (eq (extract v_6983 2 3) (expression.bv_nat 1 1));
      v_7004 <- eval (eq (extract v_6983 5 6) (expression.bv_nat 1 1));
      v_7006 <- eval (eq (extract v_6983 4 5) (expression.bv_nat 1 1));
      v_7007 <- getRegister v_2958;
      v_7008 <- eval (extract v_7007 0 32);
      v_7009 <- eval (extract v_7007 64 96);
      v_7011 <- eval (extract v_7007 32 64);
      v_7012 <- eval (extract v_7007 96 128);
      v_7016 <- eval (eq (extract v_6983 7 8) (expression.bv_nat 1 1));
      v_7018 <- eval (eq (extract v_6983 6 7) (expression.bv_nat 1 1));
      v_7022 <- eval (extract v_6988 128 160);
      v_7023 <- eval (extract v_6988 192 224);
      v_7025 <- eval (extract v_6988 160 192);
      v_7026 <- eval (extract v_6988 224 256);
      v_7032 <- eval (extract v_7007 128 160);
      v_7033 <- eval (extract v_7007 192 224);
      v_7035 <- eval (extract v_7007 160 192);
      v_7036 <- eval (extract v_7007 224 256);
      setRegister (lhs.of_reg v_2959) (concat (mux v_6985 (mux v_6987 v_6989 v_6990) (mux v_6987 v_6992 v_6993)) (concat (mux v_6997 (mux v_6999 v_6989 v_6990) (mux v_6999 v_6992 v_6993)) (concat (mux v_7004 (mux v_7006 v_7008 v_7009) (mux v_7006 v_7011 v_7012)) (concat (mux v_7016 (mux v_7018 v_7008 v_7009) (mux v_7018 v_7011 v_7012)) (concat (mux v_6985 (mux v_6987 v_7022 v_7023) (mux v_6987 v_7025 v_7026)) (concat (mux v_6997 (mux v_6999 v_7022 v_7023) (mux v_6999 v_7025 v_7026)) (concat (mux v_7004 (mux v_7006 v_7032 v_7033) (mux v_7006 v_7035 v_7036)) (mux v_7016 (mux v_7018 v_7032 v_7033) (mux v_7018 v_7035 v_7036)))))))));
      pure ()
    pat_end;
    pattern fun (v_2937 : imm int) (v_2938 : Mem) (v_2939 : reg (bv 128)) (v_2940 : reg (bv 128)) => do
      v_13264 <- eval (handleImmediateWithSignExtend v_2937 8 8);
      v_13268 <- eval (eq (extract v_13264 0 1) (expression.bv_nat 1 1));
      v_13269 <- evaluateAddress v_2938;
      v_13270 <- load v_13269 16;
      v_13271 <- eval (extract v_13270 0 32);
      v_13272 <- eval (extract v_13270 64 96);
      v_13274 <- eval (extract v_13270 32 64);
      v_13275 <- eval (extract v_13270 96 128);
      v_13281 <- eval (eq (extract v_13264 2 3) (expression.bv_nat 1 1));
      v_13288 <- eval (eq (extract v_13264 4 5) (expression.bv_nat 1 1));
      v_13289 <- getRegister v_2939;
      v_13290 <- eval (extract v_13289 0 32);
      v_13291 <- eval (extract v_13289 64 96);
      v_13293 <- eval (extract v_13289 32 64);
      v_13294 <- eval (extract v_13289 96 128);
      v_13300 <- eval (eq (extract v_13264 6 7) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_2940) (concat (mux (eq (extract v_13264 1 2) (expression.bv_nat 1 1)) (mux v_13268 v_13271 v_13272) (mux v_13268 v_13274 v_13275)) (concat (mux (eq (extract v_13264 3 4) (expression.bv_nat 1 1)) (mux v_13281 v_13271 v_13272) (mux v_13281 v_13274 v_13275)) (concat (mux (eq (extract v_13264 5 6) (expression.bv_nat 1 1)) (mux v_13288 v_13290 v_13291) (mux v_13288 v_13293 v_13294)) (mux (eq (extract v_13264 7 8) (expression.bv_nat 1 1)) (mux v_13300 v_13290 v_13291) (mux v_13300 v_13293 v_13294)))));
      pure ()
    pat_end;
    pattern fun (v_2950 : imm int) (v_2951 : Mem) (v_2952 : reg (bv 256)) (v_2953 : reg (bv 256)) => do
      v_13308 <- eval (handleImmediateWithSignExtend v_2950 8 8);
      v_13310 <- eval (eq (extract v_13308 1 2) (expression.bv_nat 1 1));
      v_13312 <- eval (eq (extract v_13308 0 1) (expression.bv_nat 1 1));
      v_13313 <- evaluateAddress v_2951;
      v_13314 <- load v_13313 32;
      v_13315 <- eval (extract v_13314 0 32);
      v_13316 <- eval (extract v_13314 64 96);
      v_13318 <- eval (extract v_13314 32 64);
      v_13319 <- eval (extract v_13314 96 128);
      v_13323 <- eval (eq (extract v_13308 3 4) (expression.bv_nat 1 1));
      v_13325 <- eval (eq (extract v_13308 2 3) (expression.bv_nat 1 1));
      v_13330 <- eval (eq (extract v_13308 5 6) (expression.bv_nat 1 1));
      v_13332 <- eval (eq (extract v_13308 4 5) (expression.bv_nat 1 1));
      v_13333 <- getRegister v_2952;
      v_13334 <- eval (extract v_13333 0 32);
      v_13335 <- eval (extract v_13333 64 96);
      v_13337 <- eval (extract v_13333 32 64);
      v_13338 <- eval (extract v_13333 96 128);
      v_13342 <- eval (eq (extract v_13308 7 8) (expression.bv_nat 1 1));
      v_13344 <- eval (eq (extract v_13308 6 7) (expression.bv_nat 1 1));
      v_13348 <- eval (extract v_13314 128 160);
      v_13349 <- eval (extract v_13314 192 224);
      v_13351 <- eval (extract v_13314 160 192);
      v_13352 <- eval (extract v_13314 224 256);
      v_13358 <- eval (extract v_13333 128 160);
      v_13359 <- eval (extract v_13333 192 224);
      v_13361 <- eval (extract v_13333 160 192);
      v_13362 <- eval (extract v_13333 224 256);
      setRegister (lhs.of_reg v_2953) (concat (mux v_13310 (mux v_13312 v_13315 v_13316) (mux v_13312 v_13318 v_13319)) (concat (mux v_13323 (mux v_13325 v_13315 v_13316) (mux v_13325 v_13318 v_13319)) (concat (mux v_13330 (mux v_13332 v_13334 v_13335) (mux v_13332 v_13337 v_13338)) (concat (mux v_13342 (mux v_13344 v_13334 v_13335) (mux v_13344 v_13337 v_13338)) (concat (mux v_13310 (mux v_13312 v_13348 v_13349) (mux v_13312 v_13351 v_13352)) (concat (mux v_13323 (mux v_13325 v_13348 v_13349) (mux v_13325 v_13351 v_13352)) (concat (mux v_13330 (mux v_13332 v_13358 v_13359) (mux v_13332 v_13361 v_13362)) (mux v_13342 (mux v_13344 v_13358 v_13359) (mux v_13344 v_13361 v_13362)))))))));
      pure ()
    pat_end
