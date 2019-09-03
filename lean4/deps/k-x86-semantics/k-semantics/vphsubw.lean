def vphsubw1 : instruction :=
  definst "vphsubw" $ do
    pattern fun (v_3269 : reg (bv 128)) (v_3270 : reg (bv 128)) (v_3271 : reg (bv 128)) => do
      v_9881 <- getRegister v_3269;
      v_9897 <- getRegister v_3270;
      setRegister (lhs.of_reg v_3271) (concat (concat (concat (concat (concat (concat (concat (sub (extract v_9881 16 32) (extract v_9881 0 16)) (sub (extract v_9881 48 64) (extract v_9881 32 48))) (sub (extract v_9881 80 96) (extract v_9881 64 80))) (sub (extract v_9881 112 128) (extract v_9881 96 112))) (sub (extract v_9897 16 32) (extract v_9897 0 16))) (sub (extract v_9897 48 64) (extract v_9897 32 48))) (sub (extract v_9897 80 96) (extract v_9897 64 80))) (sub (extract v_9897 112 128) (extract v_9897 96 112)));
      pure ()
    pat_end;
    pattern fun (v_3280 : reg (bv 256)) (v_3281 : reg (bv 256)) (v_3282 : reg (bv 256)) => do
      v_9920 <- getRegister v_3280;
      v_9936 <- getRegister v_3281;
      setRegister (lhs.of_reg v_3282) (concat (concat (concat (concat (concat (concat (concat (concat (sub (extract v_9920 16 32) (extract v_9920 0 16)) (sub (extract v_9920 48 64) (extract v_9920 32 48))) (sub (extract v_9920 80 96) (extract v_9920 64 80))) (sub (extract v_9920 112 128) (extract v_9920 96 112))) (sub (extract v_9936 16 32) (extract v_9936 0 16))) (sub (extract v_9936 48 64) (extract v_9936 32 48))) (sub (extract v_9936 80 96) (extract v_9936 64 80))) (sub (extract v_9936 112 128) (extract v_9936 96 112))) (concat (concat (concat (concat (concat (concat (concat (sub (extract v_9920 144 160) (extract v_9920 128 144)) (sub (extract v_9920 176 192) (extract v_9920 160 176))) (sub (extract v_9920 208 224) (extract v_9920 192 208))) (sub (extract v_9920 240 256) (extract v_9920 224 240))) (sub (extract v_9936 144 160) (extract v_9936 128 144))) (sub (extract v_9936 176 192) (extract v_9936 160 176))) (sub (extract v_9936 208 224) (extract v_9936 192 208))) (sub (extract v_9936 240 256) (extract v_9936 224 240))));
      pure ()
    pat_end;
    pattern fun (v_3263 : Mem) (v_3264 : reg (bv 128)) (v_3265 : reg (bv 128)) => do
      v_18866 <- evaluateAddress v_3263;
      v_18867 <- load v_18866 16;
      v_18883 <- getRegister v_3264;
      setRegister (lhs.of_reg v_3265) (concat (concat (concat (concat (concat (concat (concat (sub (extract v_18867 16 32) (extract v_18867 0 16)) (sub (extract v_18867 48 64) (extract v_18867 32 48))) (sub (extract v_18867 80 96) (extract v_18867 64 80))) (sub (extract v_18867 112 128) (extract v_18867 96 112))) (sub (extract v_18883 16 32) (extract v_18883 0 16))) (sub (extract v_18883 48 64) (extract v_18883 32 48))) (sub (extract v_18883 80 96) (extract v_18883 64 80))) (sub (extract v_18883 112 128) (extract v_18883 96 112)));
      pure ()
    pat_end;
    pattern fun (v_3274 : Mem) (v_3275 : reg (bv 256)) (v_3276 : reg (bv 256)) => do
      v_18901 <- evaluateAddress v_3274;
      v_18902 <- load v_18901 32;
      v_18918 <- getRegister v_3275;
      setRegister (lhs.of_reg v_3276) (concat (concat (concat (concat (concat (concat (concat (concat (sub (extract v_18902 16 32) (extract v_18902 0 16)) (sub (extract v_18902 48 64) (extract v_18902 32 48))) (sub (extract v_18902 80 96) (extract v_18902 64 80))) (sub (extract v_18902 112 128) (extract v_18902 96 112))) (sub (extract v_18918 16 32) (extract v_18918 0 16))) (sub (extract v_18918 48 64) (extract v_18918 32 48))) (sub (extract v_18918 80 96) (extract v_18918 64 80))) (sub (extract v_18918 112 128) (extract v_18918 96 112))) (concat (concat (concat (concat (concat (concat (concat (sub (extract v_18902 144 160) (extract v_18902 128 144)) (sub (extract v_18902 176 192) (extract v_18902 160 176))) (sub (extract v_18902 208 224) (extract v_18902 192 208))) (sub (extract v_18902 240 256) (extract v_18902 224 240))) (sub (extract v_18918 144 160) (extract v_18918 128 144))) (sub (extract v_18918 176 192) (extract v_18918 160 176))) (sub (extract v_18918 208 224) (extract v_18918 192 208))) (sub (extract v_18918 240 256) (extract v_18918 224 240))));
      pure ()
    pat_end
