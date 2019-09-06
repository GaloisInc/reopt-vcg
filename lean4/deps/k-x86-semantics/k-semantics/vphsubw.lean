def vphsubw1 : instruction :=
  definst "vphsubw" $ do
    pattern fun (v_3359 : reg (bv 128)) (v_3360 : reg (bv 128)) (v_3361 : reg (bv 128)) => do
      v_9516 <- getRegister v_3359;
      v_9532 <- getRegister v_3360;
      setRegister (lhs.of_reg v_3361) (concat (concat (concat (concat (concat (concat (concat (sub (extract v_9516 16 32) (extract v_9516 0 16)) (sub (extract v_9516 48 64) (extract v_9516 32 48))) (sub (extract v_9516 80 96) (extract v_9516 64 80))) (sub (extract v_9516 112 128) (extract v_9516 96 112))) (sub (extract v_9532 16 32) (extract v_9532 0 16))) (sub (extract v_9532 48 64) (extract v_9532 32 48))) (sub (extract v_9532 80 96) (extract v_9532 64 80))) (sub (extract v_9532 112 128) (extract v_9532 96 112)));
      pure ()
    pat_end;
    pattern fun (v_3370 : reg (bv 256)) (v_3371 : reg (bv 256)) (v_3372 : reg (bv 256)) => do
      v_9555 <- getRegister v_3370;
      v_9571 <- getRegister v_3371;
      setRegister (lhs.of_reg v_3372) (concat (concat (concat (concat (concat (concat (concat (concat (sub (extract v_9555 16 32) (extract v_9555 0 16)) (sub (extract v_9555 48 64) (extract v_9555 32 48))) (sub (extract v_9555 80 96) (extract v_9555 64 80))) (sub (extract v_9555 112 128) (extract v_9555 96 112))) (sub (extract v_9571 16 32) (extract v_9571 0 16))) (sub (extract v_9571 48 64) (extract v_9571 32 48))) (sub (extract v_9571 80 96) (extract v_9571 64 80))) (sub (extract v_9571 112 128) (extract v_9571 96 112))) (concat (concat (concat (concat (concat (concat (concat (sub (extract v_9555 144 160) (extract v_9555 128 144)) (sub (extract v_9555 176 192) (extract v_9555 160 176))) (sub (extract v_9555 208 224) (extract v_9555 192 208))) (sub (extract v_9555 240 256) (extract v_9555 224 240))) (sub (extract v_9571 144 160) (extract v_9571 128 144))) (sub (extract v_9571 176 192) (extract v_9571 160 176))) (sub (extract v_9571 208 224) (extract v_9571 192 208))) (sub (extract v_9571 240 256) (extract v_9571 224 240))));
      pure ()
    pat_end;
    pattern fun (v_3354 : Mem) (v_3355 : reg (bv 128)) (v_3356 : reg (bv 128)) => do
      v_17893 <- evaluateAddress v_3354;
      v_17894 <- load v_17893 16;
      v_17910 <- getRegister v_3355;
      setRegister (lhs.of_reg v_3356) (concat (concat (concat (concat (concat (concat (concat (sub (extract v_17894 16 32) (extract v_17894 0 16)) (sub (extract v_17894 48 64) (extract v_17894 32 48))) (sub (extract v_17894 80 96) (extract v_17894 64 80))) (sub (extract v_17894 112 128) (extract v_17894 96 112))) (sub (extract v_17910 16 32) (extract v_17910 0 16))) (sub (extract v_17910 48 64) (extract v_17910 32 48))) (sub (extract v_17910 80 96) (extract v_17910 64 80))) (sub (extract v_17910 112 128) (extract v_17910 96 112)));
      pure ()
    pat_end;
    pattern fun (v_3365 : Mem) (v_3366 : reg (bv 256)) (v_3367 : reg (bv 256)) => do
      v_17928 <- evaluateAddress v_3365;
      v_17929 <- load v_17928 32;
      v_17945 <- getRegister v_3366;
      setRegister (lhs.of_reg v_3367) (concat (concat (concat (concat (concat (concat (concat (concat (sub (extract v_17929 16 32) (extract v_17929 0 16)) (sub (extract v_17929 48 64) (extract v_17929 32 48))) (sub (extract v_17929 80 96) (extract v_17929 64 80))) (sub (extract v_17929 112 128) (extract v_17929 96 112))) (sub (extract v_17945 16 32) (extract v_17945 0 16))) (sub (extract v_17945 48 64) (extract v_17945 32 48))) (sub (extract v_17945 80 96) (extract v_17945 64 80))) (sub (extract v_17945 112 128) (extract v_17945 96 112))) (concat (concat (concat (concat (concat (concat (concat (sub (extract v_17929 144 160) (extract v_17929 128 144)) (sub (extract v_17929 176 192) (extract v_17929 160 176))) (sub (extract v_17929 208 224) (extract v_17929 192 208))) (sub (extract v_17929 240 256) (extract v_17929 224 240))) (sub (extract v_17945 144 160) (extract v_17945 128 144))) (sub (extract v_17945 176 192) (extract v_17945 160 176))) (sub (extract v_17945 208 224) (extract v_17945 192 208))) (sub (extract v_17945 240 256) (extract v_17945 224 240))));
      pure ()
    pat_end
