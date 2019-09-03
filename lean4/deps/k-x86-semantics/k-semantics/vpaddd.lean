def vpaddd1 : instruction :=
  definst "vpaddd" $ do
    pattern fun (v_3356 : reg (bv 128)) (v_3357 : reg (bv 128)) (v_3358 : reg (bv 128)) => do
      v_7735 <- getRegister v_3357;
      v_7737 <- getRegister v_3356;
      setRegister (lhs.of_reg v_3358) (concat (add (extract v_7735 0 32) (extract v_7737 0 32)) (concat (add (extract v_7735 32 64) (extract v_7737 32 64)) (concat (add (extract v_7735 64 96) (extract v_7737 64 96)) (add (extract v_7735 96 128) (extract v_7737 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_3367 : reg (bv 256)) (v_3368 : reg (bv 256)) (v_3369 : reg (bv 256)) => do
      v_7758 <- getRegister v_3368;
      v_7760 <- getRegister v_3367;
      setRegister (lhs.of_reg v_3369) (concat (add (extract v_7758 0 32) (extract v_7760 0 32)) (concat (add (extract v_7758 32 64) (extract v_7760 32 64)) (concat (add (extract v_7758 64 96) (extract v_7760 64 96)) (concat (add (extract v_7758 96 128) (extract v_7760 96 128)) (concat (add (extract v_7758 128 160) (extract v_7760 128 160)) (concat (add (extract v_7758 160 192) (extract v_7760 160 192)) (concat (add (extract v_7758 192 224) (extract v_7760 192 224)) (add (extract v_7758 224 256) (extract v_7760 224 256)))))))));
      pure ()
    pat_end;
    pattern fun (v_3351 : Mem) (v_3352 : reg (bv 128)) (v_3353 : reg (bv 128)) => do
      v_13391 <- getRegister v_3352;
      v_13393 <- evaluateAddress v_3351;
      v_13394 <- load v_13393 16;
      setRegister (lhs.of_reg v_3353) (concat (add (extract v_13391 0 32) (extract v_13394 0 32)) (concat (add (extract v_13391 32 64) (extract v_13394 32 64)) (concat (add (extract v_13391 64 96) (extract v_13394 64 96)) (add (extract v_13391 96 128) (extract v_13394 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_3362 : Mem) (v_3363 : reg (bv 256)) (v_3364 : reg (bv 256)) => do
      v_13410 <- getRegister v_3363;
      v_13412 <- evaluateAddress v_3362;
      v_13413 <- load v_13412 32;
      setRegister (lhs.of_reg v_3364) (concat (add (extract v_13410 0 32) (extract v_13413 0 32)) (concat (add (extract v_13410 32 64) (extract v_13413 32 64)) (concat (add (extract v_13410 64 96) (extract v_13413 64 96)) (concat (add (extract v_13410 96 128) (extract v_13413 96 128)) (concat (add (extract v_13410 128 160) (extract v_13413 128 160)) (concat (add (extract v_13410 160 192) (extract v_13413 160 192)) (concat (add (extract v_13410 192 224) (extract v_13413 192 224)) (add (extract v_13410 224 256) (extract v_13413 224 256)))))))));
      pure ()
    pat_end
