def vphsubw1 : instruction :=
  definst "vphsubw" $ do
    pattern fun (v_3333 : reg (bv 128)) (v_3334 : reg (bv 128)) (v_3335 : reg (bv 128)) => do
      v_9489 <- getRegister v_3333;
      v_9505 <- getRegister v_3334;
      setRegister (lhs.of_reg v_3335) (concat (concat (concat (concat (concat (concat (concat (sub (extract v_9489 16 32) (extract v_9489 0 16)) (sub (extract v_9489 48 64) (extract v_9489 32 48))) (sub (extract v_9489 80 96) (extract v_9489 64 80))) (sub (extract v_9489 112 128) (extract v_9489 96 112))) (sub (extract v_9505 16 32) (extract v_9505 0 16))) (sub (extract v_9505 48 64) (extract v_9505 32 48))) (sub (extract v_9505 80 96) (extract v_9505 64 80))) (sub (extract v_9505 112 128) (extract v_9505 96 112)));
      pure ()
    pat_end;
    pattern fun (v_3343 : reg (bv 256)) (v_3344 : reg (bv 256)) (v_3345 : reg (bv 256)) => do
      v_9528 <- getRegister v_3343;
      v_9544 <- getRegister v_3344;
      setRegister (lhs.of_reg v_3345) (concat (concat (concat (concat (concat (concat (concat (concat (sub (extract v_9528 16 32) (extract v_9528 0 16)) (sub (extract v_9528 48 64) (extract v_9528 32 48))) (sub (extract v_9528 80 96) (extract v_9528 64 80))) (sub (extract v_9528 112 128) (extract v_9528 96 112))) (sub (extract v_9544 16 32) (extract v_9544 0 16))) (sub (extract v_9544 48 64) (extract v_9544 32 48))) (sub (extract v_9544 80 96) (extract v_9544 64 80))) (sub (extract v_9544 112 128) (extract v_9544 96 112))) (concat (concat (concat (concat (concat (concat (concat (sub (extract v_9528 144 160) (extract v_9528 128 144)) (sub (extract v_9528 176 192) (extract v_9528 160 176))) (sub (extract v_9528 208 224) (extract v_9528 192 208))) (sub (extract v_9528 240 256) (extract v_9528 224 240))) (sub (extract v_9544 144 160) (extract v_9544 128 144))) (sub (extract v_9544 176 192) (extract v_9544 160 176))) (sub (extract v_9544 208 224) (extract v_9544 192 208))) (sub (extract v_9544 240 256) (extract v_9544 224 240))));
      pure ()
    pat_end;
    pattern fun (v_3327 : Mem) (v_3328 : reg (bv 128)) (v_3329 : reg (bv 128)) => do
      v_17866 <- evaluateAddress v_3327;
      v_17867 <- load v_17866 16;
      v_17883 <- getRegister v_3328;
      setRegister (lhs.of_reg v_3329) (concat (concat (concat (concat (concat (concat (concat (sub (extract v_17867 16 32) (extract v_17867 0 16)) (sub (extract v_17867 48 64) (extract v_17867 32 48))) (sub (extract v_17867 80 96) (extract v_17867 64 80))) (sub (extract v_17867 112 128) (extract v_17867 96 112))) (sub (extract v_17883 16 32) (extract v_17883 0 16))) (sub (extract v_17883 48 64) (extract v_17883 32 48))) (sub (extract v_17883 80 96) (extract v_17883 64 80))) (sub (extract v_17883 112 128) (extract v_17883 96 112)));
      pure ()
    pat_end;
    pattern fun (v_3338 : Mem) (v_3339 : reg (bv 256)) (v_3340 : reg (bv 256)) => do
      v_17901 <- evaluateAddress v_3338;
      v_17902 <- load v_17901 32;
      v_17918 <- getRegister v_3339;
      setRegister (lhs.of_reg v_3340) (concat (concat (concat (concat (concat (concat (concat (concat (sub (extract v_17902 16 32) (extract v_17902 0 16)) (sub (extract v_17902 48 64) (extract v_17902 32 48))) (sub (extract v_17902 80 96) (extract v_17902 64 80))) (sub (extract v_17902 112 128) (extract v_17902 96 112))) (sub (extract v_17918 16 32) (extract v_17918 0 16))) (sub (extract v_17918 48 64) (extract v_17918 32 48))) (sub (extract v_17918 80 96) (extract v_17918 64 80))) (sub (extract v_17918 112 128) (extract v_17918 96 112))) (concat (concat (concat (concat (concat (concat (concat (sub (extract v_17902 144 160) (extract v_17902 128 144)) (sub (extract v_17902 176 192) (extract v_17902 160 176))) (sub (extract v_17902 208 224) (extract v_17902 192 208))) (sub (extract v_17902 240 256) (extract v_17902 224 240))) (sub (extract v_17918 144 160) (extract v_17918 128 144))) (sub (extract v_17918 176 192) (extract v_17918 160 176))) (sub (extract v_17918 208 224) (extract v_17918 192 208))) (sub (extract v_17918 240 256) (extract v_17918 224 240))));
      pure ()
    pat_end
