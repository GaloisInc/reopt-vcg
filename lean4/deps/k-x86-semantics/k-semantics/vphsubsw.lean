def vphsubsw1 : instruction :=
  definst "vphsubsw" $ do
    pattern fun (v_3311 : reg (bv 128)) (v_3312 : reg (bv 128)) (v_3313 : reg (bv 128)) => do
      v_9211 <- getRegister v_3311;
      v_9216 <- eval (sub (sext (extract v_9211 16 32) 32) (sext (extract v_9211 0 16) 32));
      v_9226 <- eval (sub (sext (extract v_9211 48 64) 32) (sext (extract v_9211 32 48) 32));
      v_9236 <- eval (sub (sext (extract v_9211 80 96) 32) (sext (extract v_9211 64 80) 32));
      v_9246 <- eval (sub (sext (extract v_9211 112 128) 32) (sext (extract v_9211 96 112) 32));
      v_9252 <- getRegister v_3312;
      v_9257 <- eval (sub (sext (extract v_9252 16 32) 32) (sext (extract v_9252 0 16) 32));
      v_9267 <- eval (sub (sext (extract v_9252 48 64) 32) (sext (extract v_9252 32 48) 32));
      v_9277 <- eval (sub (sext (extract v_9252 80 96) 32) (sext (extract v_9252 64 80) 32));
      v_9287 <- eval (sub (sext (extract v_9252 112 128) 32) (sext (extract v_9252 96 112) 32));
      setRegister (lhs.of_reg v_3313) (concat (mux (sgt v_9216 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9216 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9216 16 32))) (concat (mux (sgt v_9226 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9226 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9226 16 32))) (concat (mux (sgt v_9236 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9236 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9236 16 32))) (concat (mux (sgt v_9246 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9246 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9246 16 32))) (concat (mux (sgt v_9257 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9257 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9257 16 32))) (concat (mux (sgt v_9267 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9267 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9267 16 32))) (concat (mux (sgt v_9277 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9277 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9277 16 32))) (mux (sgt v_9287 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9287 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9287 16 32))))))))));
      pure ()
    pat_end;
    pattern fun (v_3321 : reg (bv 256)) (v_3322 : reg (bv 256)) (v_3323 : reg (bv 256)) => do
      v_9306 <- getRegister v_3321;
      v_9311 <- eval (sub (sext (extract v_9306 16 32) 32) (sext (extract v_9306 0 16) 32));
      v_9321 <- eval (sub (sext (extract v_9306 48 64) 32) (sext (extract v_9306 32 48) 32));
      v_9331 <- eval (sub (sext (extract v_9306 80 96) 32) (sext (extract v_9306 64 80) 32));
      v_9341 <- eval (sub (sext (extract v_9306 112 128) 32) (sext (extract v_9306 96 112) 32));
      v_9347 <- getRegister v_3322;
      v_9352 <- eval (sub (sext (extract v_9347 16 32) 32) (sext (extract v_9347 0 16) 32));
      v_9362 <- eval (sub (sext (extract v_9347 48 64) 32) (sext (extract v_9347 32 48) 32));
      v_9372 <- eval (sub (sext (extract v_9347 80 96) 32) (sext (extract v_9347 64 80) 32));
      v_9382 <- eval (sub (sext (extract v_9347 112 128) 32) (sext (extract v_9347 96 112) 32));
      v_9392 <- eval (sub (sext (extract v_9306 144 160) 32) (sext (extract v_9306 128 144) 32));
      v_9402 <- eval (sub (sext (extract v_9306 176 192) 32) (sext (extract v_9306 160 176) 32));
      v_9412 <- eval (sub (sext (extract v_9306 208 224) 32) (sext (extract v_9306 192 208) 32));
      v_9422 <- eval (sub (sext (extract v_9306 240 256) 32) (sext (extract v_9306 224 240) 32));
      v_9432 <- eval (sub (sext (extract v_9347 144 160) 32) (sext (extract v_9347 128 144) 32));
      v_9442 <- eval (sub (sext (extract v_9347 176 192) 32) (sext (extract v_9347 160 176) 32));
      v_9452 <- eval (sub (sext (extract v_9347 208 224) 32) (sext (extract v_9347 192 208) 32));
      v_9462 <- eval (sub (sext (extract v_9347 240 256) 32) (sext (extract v_9347 224 240) 32));
      setRegister (lhs.of_reg v_3323) (concat (mux (sgt v_9311 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9311 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9311 16 32))) (concat (mux (sgt v_9321 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9321 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9321 16 32))) (concat (mux (sgt v_9331 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9331 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9331 16 32))) (concat (mux (sgt v_9341 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9341 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9341 16 32))) (concat (mux (sgt v_9352 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9352 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9352 16 32))) (concat (mux (sgt v_9362 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9362 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9362 16 32))) (concat (mux (sgt v_9372 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9372 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9372 16 32))) (concat (mux (sgt v_9382 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9382 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9382 16 32))) (concat (mux (sgt v_9392 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9392 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9392 16 32))) (concat (mux (sgt v_9402 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9402 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9402 16 32))) (concat (mux (sgt v_9412 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9412 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9412 16 32))) (concat (mux (sgt v_9422 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9422 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9422 16 32))) (concat (mux (sgt v_9432 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9432 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9432 16 32))) (concat (mux (sgt v_9442 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9442 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9442 16 32))) (concat (mux (sgt v_9452 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9452 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9452 16 32))) (mux (sgt v_9462 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9462 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9462 16 32))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3305 : Mem) (v_3306 : reg (bv 128)) (v_3307 : reg (bv 128)) => do
      v_17596 <- evaluateAddress v_3305;
      v_17597 <- load v_17596 16;
      v_17602 <- eval (sub (sext (extract v_17597 16 32) 32) (sext (extract v_17597 0 16) 32));
      v_17612 <- eval (sub (sext (extract v_17597 48 64) 32) (sext (extract v_17597 32 48) 32));
      v_17622 <- eval (sub (sext (extract v_17597 80 96) 32) (sext (extract v_17597 64 80) 32));
      v_17632 <- eval (sub (sext (extract v_17597 112 128) 32) (sext (extract v_17597 96 112) 32));
      v_17638 <- getRegister v_3306;
      v_17643 <- eval (sub (sext (extract v_17638 16 32) 32) (sext (extract v_17638 0 16) 32));
      v_17653 <- eval (sub (sext (extract v_17638 48 64) 32) (sext (extract v_17638 32 48) 32));
      v_17663 <- eval (sub (sext (extract v_17638 80 96) 32) (sext (extract v_17638 64 80) 32));
      v_17673 <- eval (sub (sext (extract v_17638 112 128) 32) (sext (extract v_17638 96 112) 32));
      setRegister (lhs.of_reg v_3307) (concat (mux (sgt v_17602 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17602 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17602 16 32))) (concat (mux (sgt v_17612 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17612 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17612 16 32))) (concat (mux (sgt v_17622 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17622 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17622 16 32))) (concat (mux (sgt v_17632 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17632 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17632 16 32))) (concat (mux (sgt v_17643 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17643 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17643 16 32))) (concat (mux (sgt v_17653 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17653 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17653 16 32))) (concat (mux (sgt v_17663 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17663 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17663 16 32))) (mux (sgt v_17673 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17673 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17673 16 32))))))))));
      pure ()
    pat_end;
    pattern fun (v_3316 : Mem) (v_3317 : reg (bv 256)) (v_3318 : reg (bv 256)) => do
      v_17687 <- evaluateAddress v_3316;
      v_17688 <- load v_17687 32;
      v_17693 <- eval (sub (sext (extract v_17688 16 32) 32) (sext (extract v_17688 0 16) 32));
      v_17703 <- eval (sub (sext (extract v_17688 48 64) 32) (sext (extract v_17688 32 48) 32));
      v_17713 <- eval (sub (sext (extract v_17688 80 96) 32) (sext (extract v_17688 64 80) 32));
      v_17723 <- eval (sub (sext (extract v_17688 112 128) 32) (sext (extract v_17688 96 112) 32));
      v_17729 <- getRegister v_3317;
      v_17734 <- eval (sub (sext (extract v_17729 16 32) 32) (sext (extract v_17729 0 16) 32));
      v_17744 <- eval (sub (sext (extract v_17729 48 64) 32) (sext (extract v_17729 32 48) 32));
      v_17754 <- eval (sub (sext (extract v_17729 80 96) 32) (sext (extract v_17729 64 80) 32));
      v_17764 <- eval (sub (sext (extract v_17729 112 128) 32) (sext (extract v_17729 96 112) 32));
      v_17774 <- eval (sub (sext (extract v_17688 144 160) 32) (sext (extract v_17688 128 144) 32));
      v_17784 <- eval (sub (sext (extract v_17688 176 192) 32) (sext (extract v_17688 160 176) 32));
      v_17794 <- eval (sub (sext (extract v_17688 208 224) 32) (sext (extract v_17688 192 208) 32));
      v_17804 <- eval (sub (sext (extract v_17688 240 256) 32) (sext (extract v_17688 224 240) 32));
      v_17814 <- eval (sub (sext (extract v_17729 144 160) 32) (sext (extract v_17729 128 144) 32));
      v_17824 <- eval (sub (sext (extract v_17729 176 192) 32) (sext (extract v_17729 160 176) 32));
      v_17834 <- eval (sub (sext (extract v_17729 208 224) 32) (sext (extract v_17729 192 208) 32));
      v_17844 <- eval (sub (sext (extract v_17729 240 256) 32) (sext (extract v_17729 224 240) 32));
      setRegister (lhs.of_reg v_3318) (concat (mux (sgt v_17693 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17693 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17693 16 32))) (concat (mux (sgt v_17703 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17703 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17703 16 32))) (concat (mux (sgt v_17713 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17713 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17713 16 32))) (concat (mux (sgt v_17723 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17723 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17723 16 32))) (concat (mux (sgt v_17734 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17734 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17734 16 32))) (concat (mux (sgt v_17744 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17744 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17744 16 32))) (concat (mux (sgt v_17754 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17754 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17754 16 32))) (concat (mux (sgt v_17764 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17764 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17764 16 32))) (concat (mux (sgt v_17774 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17774 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17774 16 32))) (concat (mux (sgt v_17784 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17784 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17784 16 32))) (concat (mux (sgt v_17794 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17794 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17794 16 32))) (concat (mux (sgt v_17804 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17804 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17804 16 32))) (concat (mux (sgt v_17814 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17814 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17814 16 32))) (concat (mux (sgt v_17824 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17824 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17824 16 32))) (concat (mux (sgt v_17834 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17834 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17834 16 32))) (mux (sgt v_17844 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17844 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17844 16 32))))))))))))))))));
      pure ()
    pat_end
