def vpaddd1 : instruction :=
  definst "vpaddd" $ do
    pattern fun (v_3344 : reg (bv 128)) (v_3345 : reg (bv 128)) (v_3346 : reg (bv 128)) => do
      v_7290 <- getRegister v_3345;
      v_7292 <- getRegister v_3344;
      setRegister (lhs.of_reg v_3346) (concat (add (extract v_7290 0 32) (extract v_7292 0 32)) (concat (add (extract v_7290 32 64) (extract v_7292 32 64)) (concat (add (extract v_7290 64 96) (extract v_7292 64 96)) (add (extract v_7290 96 128) (extract v_7292 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_3355 : reg (bv 256)) (v_3356 : reg (bv 256)) (v_3357 : reg (bv 256)) => do
      v_7313 <- getRegister v_3356;
      v_7315 <- getRegister v_3355;
      setRegister (lhs.of_reg v_3357) (concat (add (extract v_7313 0 32) (extract v_7315 0 32)) (concat (add (extract v_7313 32 64) (extract v_7315 32 64)) (concat (add (extract v_7313 64 96) (extract v_7315 64 96)) (concat (add (extract v_7313 96 128) (extract v_7315 96 128)) (concat (add (extract v_7313 128 160) (extract v_7315 128 160)) (concat (add (extract v_7313 160 192) (extract v_7315 160 192)) (concat (add (extract v_7313 192 224) (extract v_7315 192 224)) (add (extract v_7313 224 256) (extract v_7315 224 256)))))))));
      pure ()
    pat_end;
    pattern fun (v_3338 : Mem) (v_3339 : reg (bv 128)) (v_3340 : reg (bv 128)) => do
      v_12514 <- getRegister v_3339;
      v_12516 <- evaluateAddress v_3338;
      v_12517 <- load v_12516 16;
      setRegister (lhs.of_reg v_3340) (concat (add (extract v_12514 0 32) (extract v_12517 0 32)) (concat (add (extract v_12514 32 64) (extract v_12517 32 64)) (concat (add (extract v_12514 64 96) (extract v_12517 64 96)) (add (extract v_12514 96 128) (extract v_12517 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_3349 : Mem) (v_3350 : reg (bv 256)) (v_3351 : reg (bv 256)) => do
      v_12533 <- getRegister v_3350;
      v_12535 <- evaluateAddress v_3349;
      v_12536 <- load v_12535 32;
      setRegister (lhs.of_reg v_3351) (concat (add (extract v_12533 0 32) (extract v_12536 0 32)) (concat (add (extract v_12533 32 64) (extract v_12536 32 64)) (concat (add (extract v_12533 64 96) (extract v_12536 64 96)) (concat (add (extract v_12533 96 128) (extract v_12536 96 128)) (concat (add (extract v_12533 128 160) (extract v_12536 128 160)) (concat (add (extract v_12533 160 192) (extract v_12536 160 192)) (concat (add (extract v_12533 192 224) (extract v_12536 192 224)) (add (extract v_12533 224 256) (extract v_12536 224 256)))))))));
      pure ()
    pat_end
