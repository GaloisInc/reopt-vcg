def vpblendw1 : instruction :=
  definst "vpblendw" $ do
    pattern fun (v_2660 : imm int) (v_2664 : reg (bv 128)) (v_2665 : reg (bv 128)) (v_2666 : reg (bv 128)) => do
      v_6980 <- eval (handleImmediateWithSignExtend v_2660 8 8);
      v_6983 <- getRegister v_2665;
      v_6985 <- getRegister v_2664;
      setRegister (lhs.of_reg v_2666) (concat (mux (eq (extract v_6980 0 1) (expression.bv_nat 1 0)) (extract v_6983 0 16) (extract v_6985 0 16)) (concat (mux (eq (extract v_6980 1 2) (expression.bv_nat 1 0)) (extract v_6983 16 32) (extract v_6985 16 32)) (concat (mux (eq (extract v_6980 2 3) (expression.bv_nat 1 0)) (extract v_6983 32 48) (extract v_6985 32 48)) (concat (mux (eq (extract v_6980 3 4) (expression.bv_nat 1 0)) (extract v_6983 48 64) (extract v_6985 48 64)) (concat (mux (eq (extract v_6980 4 5) (expression.bv_nat 1 0)) (extract v_6983 64 80) (extract v_6985 64 80)) (concat (mux (eq (extract v_6980 5 6) (expression.bv_nat 1 0)) (extract v_6983 80 96) (extract v_6985 80 96)) (concat (mux (eq (extract v_6980 6 7) (expression.bv_nat 1 0)) (extract v_6983 96 112) (extract v_6985 96 112)) (mux (eq (extract v_6980 7 8) (expression.bv_nat 1 0)) (extract v_6983 112 128) (extract v_6985 112 128)))))))));
      pure ()
    pat_end;
    pattern fun (v_2673 : imm int) (v_2677 : reg (bv 256)) (v_2678 : reg (bv 256)) (v_2679 : reg (bv 256)) => do
      v_7037 <- eval (handleImmediateWithSignExtend v_2673 8 8);
      v_7039 <- eval (eq (extract v_7037 0 1) (expression.bv_nat 1 0));
      v_7040 <- getRegister v_2678;
      v_7042 <- getRegister v_2677;
      v_7046 <- eval (eq (extract v_7037 1 2) (expression.bv_nat 1 0));
      v_7051 <- eval (eq (extract v_7037 2 3) (expression.bv_nat 1 0));
      v_7056 <- eval (eq (extract v_7037 3 4) (expression.bv_nat 1 0));
      v_7061 <- eval (eq (extract v_7037 4 5) (expression.bv_nat 1 0));
      v_7066 <- eval (eq (extract v_7037 5 6) (expression.bv_nat 1 0));
      v_7071 <- eval (eq (extract v_7037 6 7) (expression.bv_nat 1 0));
      v_7076 <- eval (eq (extract v_7037 7 8) (expression.bv_nat 1 0));
      setRegister (lhs.of_reg v_2679) (concat (mux v_7039 (extract v_7040 0 16) (extract v_7042 0 16)) (concat (mux v_7046 (extract v_7040 16 32) (extract v_7042 16 32)) (concat (mux v_7051 (extract v_7040 32 48) (extract v_7042 32 48)) (concat (mux v_7056 (extract v_7040 48 64) (extract v_7042 48 64)) (concat (mux v_7061 (extract v_7040 64 80) (extract v_7042 64 80)) (concat (mux v_7066 (extract v_7040 80 96) (extract v_7042 80 96)) (concat (mux v_7071 (extract v_7040 96 112) (extract v_7042 96 112)) (concat (mux v_7076 (extract v_7040 112 128) (extract v_7042 112 128)) (concat (mux v_7039 (extract v_7040 128 144) (extract v_7042 128 144)) (concat (mux v_7046 (extract v_7040 144 160) (extract v_7042 144 160)) (concat (mux v_7051 (extract v_7040 160 176) (extract v_7042 160 176)) (concat (mux v_7056 (extract v_7040 176 192) (extract v_7042 176 192)) (concat (mux v_7061 (extract v_7040 192 208) (extract v_7042 192 208)) (concat (mux v_7066 (extract v_7040 208 224) (extract v_7042 208 224)) (concat (mux v_7071 (extract v_7040 224 240) (extract v_7042 224 240)) (mux v_7076 (extract v_7040 240 256) (extract v_7042 240 256)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2654 : imm int) (v_2657 : Mem) (v_2658 : reg (bv 128)) (v_2659 : reg (bv 128)) => do
      v_16257 <- eval (handleImmediateWithSignExtend v_2654 8 8);
      v_16260 <- getRegister v_2658;
      v_16262 <- evaluateAddress v_2657;
      v_16263 <- load v_16262 16;
      setRegister (lhs.of_reg v_2659) (concat (mux (eq (extract v_16257 0 1) (expression.bv_nat 1 0)) (extract v_16260 0 16) (extract v_16263 0 16)) (concat (mux (eq (extract v_16257 1 2) (expression.bv_nat 1 0)) (extract v_16260 16 32) (extract v_16263 16 32)) (concat (mux (eq (extract v_16257 2 3) (expression.bv_nat 1 0)) (extract v_16260 32 48) (extract v_16263 32 48)) (concat (mux (eq (extract v_16257 3 4) (expression.bv_nat 1 0)) (extract v_16260 48 64) (extract v_16263 48 64)) (concat (mux (eq (extract v_16257 4 5) (expression.bv_nat 1 0)) (extract v_16260 64 80) (extract v_16263 64 80)) (concat (mux (eq (extract v_16257 5 6) (expression.bv_nat 1 0)) (extract v_16260 80 96) (extract v_16263 80 96)) (concat (mux (eq (extract v_16257 6 7) (expression.bv_nat 1 0)) (extract v_16260 96 112) (extract v_16263 96 112)) (mux (eq (extract v_16257 7 8) (expression.bv_nat 1 0)) (extract v_16260 112 128) (extract v_16263 112 128)))))))));
      pure ()
    pat_end;
    pattern fun (v_2667 : imm int) (v_2670 : Mem) (v_2671 : reg (bv 256)) (v_2672 : reg (bv 256)) => do
      v_16309 <- eval (handleImmediateWithSignExtend v_2667 8 8);
      v_16311 <- eval (eq (extract v_16309 0 1) (expression.bv_nat 1 0));
      v_16312 <- getRegister v_2671;
      v_16314 <- evaluateAddress v_2670;
      v_16315 <- load v_16314 32;
      v_16319 <- eval (eq (extract v_16309 1 2) (expression.bv_nat 1 0));
      v_16324 <- eval (eq (extract v_16309 2 3) (expression.bv_nat 1 0));
      v_16329 <- eval (eq (extract v_16309 3 4) (expression.bv_nat 1 0));
      v_16334 <- eval (eq (extract v_16309 4 5) (expression.bv_nat 1 0));
      v_16339 <- eval (eq (extract v_16309 5 6) (expression.bv_nat 1 0));
      v_16344 <- eval (eq (extract v_16309 6 7) (expression.bv_nat 1 0));
      v_16349 <- eval (eq (extract v_16309 7 8) (expression.bv_nat 1 0));
      setRegister (lhs.of_reg v_2672) (concat (mux v_16311 (extract v_16312 0 16) (extract v_16315 0 16)) (concat (mux v_16319 (extract v_16312 16 32) (extract v_16315 16 32)) (concat (mux v_16324 (extract v_16312 32 48) (extract v_16315 32 48)) (concat (mux v_16329 (extract v_16312 48 64) (extract v_16315 48 64)) (concat (mux v_16334 (extract v_16312 64 80) (extract v_16315 64 80)) (concat (mux v_16339 (extract v_16312 80 96) (extract v_16315 80 96)) (concat (mux v_16344 (extract v_16312 96 112) (extract v_16315 96 112)) (concat (mux v_16349 (extract v_16312 112 128) (extract v_16315 112 128)) (concat (mux v_16311 (extract v_16312 128 144) (extract v_16315 128 144)) (concat (mux v_16319 (extract v_16312 144 160) (extract v_16315 144 160)) (concat (mux v_16324 (extract v_16312 160 176) (extract v_16315 160 176)) (concat (mux v_16329 (extract v_16312 176 192) (extract v_16315 176 192)) (concat (mux v_16334 (extract v_16312 192 208) (extract v_16315 192 208)) (concat (mux v_16339 (extract v_16312 208 224) (extract v_16315 208 224)) (concat (mux v_16344 (extract v_16312 224 240) (extract v_16315 224 240)) (mux v_16349 (extract v_16312 240 256) (extract v_16315 240 256)))))))))))))))));
      pure ()
    pat_end
