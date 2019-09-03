def vpackssdw1 : instruction :=
  definst "vpackssdw" $ do
    pattern fun (v_3246 : reg (bv 128)) (v_3247 : reg (bv 128)) (v_3248 : reg (bv 128)) => do
      v_6465 <- getRegister v_3246;
      v_6466 <- eval (extract v_6465 0 32);
      v_6472 <- eval (extract v_6465 32 64);
      v_6478 <- eval (extract v_6465 64 96);
      v_6484 <- eval (extract v_6465 96 128);
      v_6490 <- getRegister v_3247;
      v_6491 <- eval (extract v_6490 0 32);
      v_6497 <- eval (extract v_6490 32 64);
      v_6503 <- eval (extract v_6490 64 96);
      v_6509 <- eval (extract v_6490 96 128);
      setRegister (lhs.of_reg v_3248) (concat (mux (sgt v_6466 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6466 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6465 16 32))) (concat (mux (sgt v_6472 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6472 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6465 48 64))) (concat (mux (sgt v_6478 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6478 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6465 80 96))) (concat (mux (sgt v_6484 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6484 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6465 112 128))) (concat (mux (sgt v_6491 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6491 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6490 16 32))) (concat (mux (sgt v_6497 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6497 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6490 48 64))) (concat (mux (sgt v_6503 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6503 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6490 80 96))) (mux (sgt v_6509 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6509 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6490 112 128))))))))));
      pure ()
    pat_end;
    pattern fun (v_3257 : reg (bv 256)) (v_3258 : reg (bv 256)) (v_3259 : reg (bv 256)) => do
      v_6528 <- getRegister v_3257;
      v_6529 <- eval (extract v_6528 0 32);
      v_6535 <- eval (extract v_6528 32 64);
      v_6541 <- eval (extract v_6528 64 96);
      v_6547 <- eval (extract v_6528 96 128);
      v_6553 <- getRegister v_3258;
      v_6554 <- eval (extract v_6553 0 32);
      v_6560 <- eval (extract v_6553 32 64);
      v_6566 <- eval (extract v_6553 64 96);
      v_6572 <- eval (extract v_6553 96 128);
      v_6578 <- eval (extract v_6528 128 160);
      v_6584 <- eval (extract v_6528 160 192);
      v_6590 <- eval (extract v_6528 192 224);
      v_6596 <- eval (extract v_6528 224 256);
      v_6602 <- eval (extract v_6553 128 160);
      v_6608 <- eval (extract v_6553 160 192);
      v_6614 <- eval (extract v_6553 192 224);
      v_6620 <- eval (extract v_6553 224 256);
      setRegister (lhs.of_reg v_3259) (concat (mux (sgt v_6529 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6529 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6528 16 32))) (concat (mux (sgt v_6535 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6535 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6528 48 64))) (concat (mux (sgt v_6541 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6541 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6528 80 96))) (concat (mux (sgt v_6547 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6547 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6528 112 128))) (concat (mux (sgt v_6554 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6554 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6553 16 32))) (concat (mux (sgt v_6560 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6560 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6553 48 64))) (concat (mux (sgt v_6566 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6566 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6553 80 96))) (concat (mux (sgt v_6572 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6572 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6553 112 128))) (concat (mux (sgt v_6578 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6578 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6528 144 160))) (concat (mux (sgt v_6584 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6584 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6528 176 192))) (concat (mux (sgt v_6590 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6590 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6528 208 224))) (concat (mux (sgt v_6596 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6596 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6528 240 256))) (concat (mux (sgt v_6602 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6602 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6553 144 160))) (concat (mux (sgt v_6608 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6608 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6553 176 192))) (concat (mux (sgt v_6614 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6614 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6553 208 224))) (mux (sgt v_6620 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6620 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6553 240 256))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3241 : Mem) (v_3242 : reg (bv 128)) (v_3243 : reg (bv 128)) => do
      v_12161 <- evaluateAddress v_3241;
      v_12162 <- load v_12161 16;
      v_12163 <- eval (extract v_12162 0 32);
      v_12169 <- eval (extract v_12162 32 64);
      v_12175 <- eval (extract v_12162 64 96);
      v_12181 <- eval (extract v_12162 96 128);
      v_12187 <- getRegister v_3242;
      v_12188 <- eval (extract v_12187 0 32);
      v_12194 <- eval (extract v_12187 32 64);
      v_12200 <- eval (extract v_12187 64 96);
      v_12206 <- eval (extract v_12187 96 128);
      setRegister (lhs.of_reg v_3243) (concat (mux (sgt v_12163 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_12163 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_12162 16 32))) (concat (mux (sgt v_12169 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_12169 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_12162 48 64))) (concat (mux (sgt v_12175 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_12175 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_12162 80 96))) (concat (mux (sgt v_12181 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_12181 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_12162 112 128))) (concat (mux (sgt v_12188 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_12188 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_12187 16 32))) (concat (mux (sgt v_12194 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_12194 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_12187 48 64))) (concat (mux (sgt v_12200 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_12200 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_12187 80 96))) (mux (sgt v_12206 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_12206 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_12187 112 128))))))))));
      pure ()
    pat_end;
    pattern fun (v_3252 : Mem) (v_3253 : reg (bv 256)) (v_3254 : reg (bv 256)) => do
      v_12220 <- evaluateAddress v_3252;
      v_12221 <- load v_12220 32;
      v_12222 <- eval (extract v_12221 0 32);
      v_12228 <- eval (extract v_12221 32 64);
      v_12234 <- eval (extract v_12221 64 96);
      v_12240 <- eval (extract v_12221 96 128);
      v_12246 <- getRegister v_3253;
      v_12247 <- eval (extract v_12246 0 32);
      v_12253 <- eval (extract v_12246 32 64);
      v_12259 <- eval (extract v_12246 64 96);
      v_12265 <- eval (extract v_12246 96 128);
      v_12271 <- eval (extract v_12221 128 160);
      v_12277 <- eval (extract v_12221 160 192);
      v_12283 <- eval (extract v_12221 192 224);
      v_12289 <- eval (extract v_12221 224 256);
      v_12295 <- eval (extract v_12246 128 160);
      v_12301 <- eval (extract v_12246 160 192);
      v_12307 <- eval (extract v_12246 192 224);
      v_12313 <- eval (extract v_12246 224 256);
      setRegister (lhs.of_reg v_3254) (concat (mux (sgt v_12222 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_12222 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_12221 16 32))) (concat (mux (sgt v_12228 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_12228 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_12221 48 64))) (concat (mux (sgt v_12234 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_12234 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_12221 80 96))) (concat (mux (sgt v_12240 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_12240 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_12221 112 128))) (concat (mux (sgt v_12247 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_12247 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_12246 16 32))) (concat (mux (sgt v_12253 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_12253 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_12246 48 64))) (concat (mux (sgt v_12259 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_12259 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_12246 80 96))) (concat (mux (sgt v_12265 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_12265 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_12246 112 128))) (concat (mux (sgt v_12271 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_12271 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_12221 144 160))) (concat (mux (sgt v_12277 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_12277 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_12221 176 192))) (concat (mux (sgt v_12283 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_12283 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_12221 208 224))) (concat (mux (sgt v_12289 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_12289 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_12221 240 256))) (concat (mux (sgt v_12295 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_12295 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_12246 144 160))) (concat (mux (sgt v_12301 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_12301 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_12246 176 192))) (concat (mux (sgt v_12307 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_12307 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_12246 208 224))) (mux (sgt v_12313 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_12313 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_12246 240 256))))))))))))))))));
      pure ()
    pat_end
