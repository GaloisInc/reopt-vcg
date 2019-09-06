def vpackssdw1 : instruction :=
  definst "vpackssdw" $ do
    pattern fun (v_3322 : reg (bv 128)) (v_3323 : reg (bv 128)) (v_3324 : reg (bv 128)) => do
      v_5937 <- getRegister v_3322;
      v_5938 <- eval (extract v_5937 0 32);
      v_5944 <- eval (extract v_5937 32 64);
      v_5950 <- eval (extract v_5937 64 96);
      v_5956 <- eval (extract v_5937 96 128);
      v_5962 <- getRegister v_3323;
      v_5963 <- eval (extract v_5962 0 32);
      v_5969 <- eval (extract v_5962 32 64);
      v_5975 <- eval (extract v_5962 64 96);
      v_5981 <- eval (extract v_5962 96 128);
      setRegister (lhs.of_reg v_3324) (concat (mux (sgt v_5938 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5938 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5937 16 32))) (concat (mux (sgt v_5944 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5944 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5937 48 64))) (concat (mux (sgt v_5950 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5950 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5937 80 96))) (concat (mux (sgt v_5956 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5956 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5937 112 128))) (concat (mux (sgt v_5963 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5963 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5962 16 32))) (concat (mux (sgt v_5969 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5969 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5962 48 64))) (concat (mux (sgt v_5975 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5975 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5962 80 96))) (mux (sgt v_5981 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5981 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5962 112 128))))))))));
      pure ()
    pat_end;
    pattern fun (v_3333 : reg (bv 256)) (v_3334 : reg (bv 256)) (v_3335 : reg (bv 256)) => do
      v_6000 <- getRegister v_3333;
      v_6001 <- eval (extract v_6000 0 32);
      v_6007 <- eval (extract v_6000 32 64);
      v_6013 <- eval (extract v_6000 64 96);
      v_6019 <- eval (extract v_6000 96 128);
      v_6025 <- getRegister v_3334;
      v_6026 <- eval (extract v_6025 0 32);
      v_6032 <- eval (extract v_6025 32 64);
      v_6038 <- eval (extract v_6025 64 96);
      v_6044 <- eval (extract v_6025 96 128);
      v_6050 <- eval (extract v_6000 128 160);
      v_6056 <- eval (extract v_6000 160 192);
      v_6062 <- eval (extract v_6000 192 224);
      v_6068 <- eval (extract v_6000 224 256);
      v_6074 <- eval (extract v_6025 128 160);
      v_6080 <- eval (extract v_6025 160 192);
      v_6086 <- eval (extract v_6025 192 224);
      v_6092 <- eval (extract v_6025 224 256);
      setRegister (lhs.of_reg v_3335) (concat (mux (sgt v_6001 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6001 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6000 16 32))) (concat (mux (sgt v_6007 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6007 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6000 48 64))) (concat (mux (sgt v_6013 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6013 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6000 80 96))) (concat (mux (sgt v_6019 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6019 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6000 112 128))) (concat (mux (sgt v_6026 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6026 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6025 16 32))) (concat (mux (sgt v_6032 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6032 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6025 48 64))) (concat (mux (sgt v_6038 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6038 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6025 80 96))) (concat (mux (sgt v_6044 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6044 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6025 112 128))) (concat (mux (sgt v_6050 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6050 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6000 144 160))) (concat (mux (sgt v_6056 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6056 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6000 176 192))) (concat (mux (sgt v_6062 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6062 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6000 208 224))) (concat (mux (sgt v_6068 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6068 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6000 240 256))) (concat (mux (sgt v_6074 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6074 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6025 144 160))) (concat (mux (sgt v_6080 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6080 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6025 176 192))) (concat (mux (sgt v_6086 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6086 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6025 208 224))) (mux (sgt v_6092 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6092 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6025 240 256))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3317 : Mem) (v_3318 : reg (bv 128)) (v_3319 : reg (bv 128)) => do
      v_11009 <- evaluateAddress v_3317;
      v_11010 <- load v_11009 16;
      v_11011 <- eval (extract v_11010 0 32);
      v_11017 <- eval (extract v_11010 32 64);
      v_11023 <- eval (extract v_11010 64 96);
      v_11029 <- eval (extract v_11010 96 128);
      v_11035 <- getRegister v_3318;
      v_11036 <- eval (extract v_11035 0 32);
      v_11042 <- eval (extract v_11035 32 64);
      v_11048 <- eval (extract v_11035 64 96);
      v_11054 <- eval (extract v_11035 96 128);
      setRegister (lhs.of_reg v_3319) (concat (mux (sgt v_11011 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11011 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11010 16 32))) (concat (mux (sgt v_11017 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11017 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11010 48 64))) (concat (mux (sgt v_11023 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11023 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11010 80 96))) (concat (mux (sgt v_11029 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11029 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11010 112 128))) (concat (mux (sgt v_11036 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11036 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11035 16 32))) (concat (mux (sgt v_11042 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11042 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11035 48 64))) (concat (mux (sgt v_11048 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11048 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11035 80 96))) (mux (sgt v_11054 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11054 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11035 112 128))))))))));
      pure ()
    pat_end;
    pattern fun (v_3328 : Mem) (v_3329 : reg (bv 256)) (v_3330 : reg (bv 256)) => do
      v_11068 <- evaluateAddress v_3328;
      v_11069 <- load v_11068 32;
      v_11070 <- eval (extract v_11069 0 32);
      v_11076 <- eval (extract v_11069 32 64);
      v_11082 <- eval (extract v_11069 64 96);
      v_11088 <- eval (extract v_11069 96 128);
      v_11094 <- getRegister v_3329;
      v_11095 <- eval (extract v_11094 0 32);
      v_11101 <- eval (extract v_11094 32 64);
      v_11107 <- eval (extract v_11094 64 96);
      v_11113 <- eval (extract v_11094 96 128);
      v_11119 <- eval (extract v_11069 128 160);
      v_11125 <- eval (extract v_11069 160 192);
      v_11131 <- eval (extract v_11069 192 224);
      v_11137 <- eval (extract v_11069 224 256);
      v_11143 <- eval (extract v_11094 128 160);
      v_11149 <- eval (extract v_11094 160 192);
      v_11155 <- eval (extract v_11094 192 224);
      v_11161 <- eval (extract v_11094 224 256);
      setRegister (lhs.of_reg v_3330) (concat (mux (sgt v_11070 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11070 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11069 16 32))) (concat (mux (sgt v_11076 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11076 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11069 48 64))) (concat (mux (sgt v_11082 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11082 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11069 80 96))) (concat (mux (sgt v_11088 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11088 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11069 112 128))) (concat (mux (sgt v_11095 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11095 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11094 16 32))) (concat (mux (sgt v_11101 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11101 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11094 48 64))) (concat (mux (sgt v_11107 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11107 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11094 80 96))) (concat (mux (sgt v_11113 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11113 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11094 112 128))) (concat (mux (sgt v_11119 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11119 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11069 144 160))) (concat (mux (sgt v_11125 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11125 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11069 176 192))) (concat (mux (sgt v_11131 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11131 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11069 208 224))) (concat (mux (sgt v_11137 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11137 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11069 240 256))) (concat (mux (sgt v_11143 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11143 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11094 144 160))) (concat (mux (sgt v_11149 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11149 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11094 176 192))) (concat (mux (sgt v_11155 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11155 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11094 208 224))) (mux (sgt v_11161 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11161 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11094 240 256))))))))))))))))));
      pure ()
    pat_end
