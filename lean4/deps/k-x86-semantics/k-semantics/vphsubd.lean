def vphsubd1 : instruction :=
  definst "vphsubd" $ do
    pattern fun (v_3315 : reg (bv 128)) (v_3316 : reg (bv 128)) (v_3317 : reg (bv 128)) => do
      v_9176 <- getRegister v_3315;
      v_9184 <- getRegister v_3316;
      setRegister (lhs.of_reg v_3317) (concat (concat (concat (sub (extract v_9176 32 64) (extract v_9176 0 32)) (sub (extract v_9176 96 128) (extract v_9176 64 96))) (sub (extract v_9184 32 64) (extract v_9184 0 32))) (sub (extract v_9184 96 128) (extract v_9184 64 96)));
      pure ()
    pat_end;
    pattern fun (v_3326 : reg (bv 256)) (v_3327 : reg (bv 256)) (v_3328 : reg (bv 256)) => do
      v_9199 <- getRegister v_3326;
      v_9207 <- getRegister v_3327;
      setRegister (lhs.of_reg v_3328) (concat (concat (concat (concat (sub (extract v_9199 32 64) (extract v_9199 0 32)) (sub (extract v_9199 96 128) (extract v_9199 64 96))) (sub (extract v_9207 32 64) (extract v_9207 0 32))) (sub (extract v_9207 96 128) (extract v_9207 64 96))) (concat (concat (concat (sub (extract v_9199 160 192) (extract v_9199 128 160)) (sub (extract v_9199 224 256) (extract v_9199 192 224))) (sub (extract v_9207 160 192) (extract v_9207 128 160))) (sub (extract v_9207 224 256) (extract v_9207 192 224))));
      pure ()
    pat_end;
    pattern fun (v_3310 : Mem) (v_3311 : reg (bv 128)) (v_3312 : reg (bv 128)) => do
      v_17569 <- evaluateAddress v_3310;
      v_17570 <- load v_17569 16;
      v_17578 <- getRegister v_3311;
      setRegister (lhs.of_reg v_3312) (concat (concat (concat (sub (extract v_17570 32 64) (extract v_17570 0 32)) (sub (extract v_17570 96 128) (extract v_17570 64 96))) (sub (extract v_17578 32 64) (extract v_17578 0 32))) (sub (extract v_17578 96 128) (extract v_17578 64 96)));
      pure ()
    pat_end;
    pattern fun (v_3321 : Mem) (v_3322 : reg (bv 256)) (v_3323 : reg (bv 256)) => do
      v_17588 <- evaluateAddress v_3321;
      v_17589 <- load v_17588 32;
      v_17597 <- getRegister v_3322;
      setRegister (lhs.of_reg v_3323) (concat (concat (concat (concat (sub (extract v_17589 32 64) (extract v_17589 0 32)) (sub (extract v_17589 96 128) (extract v_17589 64 96))) (sub (extract v_17597 32 64) (extract v_17597 0 32))) (sub (extract v_17597 96 128) (extract v_17597 64 96))) (concat (concat (concat (sub (extract v_17589 160 192) (extract v_17589 128 160)) (sub (extract v_17589 224 256) (extract v_17589 192 224))) (sub (extract v_17597 160 192) (extract v_17597 128 160))) (sub (extract v_17597 224 256) (extract v_17597 192 224))));
      pure ()
    pat_end
