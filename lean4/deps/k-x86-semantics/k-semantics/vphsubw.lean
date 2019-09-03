def vphsubw1 : instruction :=
  definst "vphsubw" $ do
    pattern fun (v_3279 : reg (bv 128)) (v_3280 : reg (bv 128)) (v_3281 : reg (bv 128)) => do
      v_9634 <- getRegister v_3279;
      v_9650 <- getRegister v_3280;
      setRegister (lhs.of_reg v_3281) (concat (concat (concat (concat (concat (concat (concat (sub (extract v_9634 16 32) (extract v_9634 0 16)) (sub (extract v_9634 48 64) (extract v_9634 32 48))) (sub (extract v_9634 80 96) (extract v_9634 64 80))) (sub (extract v_9634 112 128) (extract v_9634 96 112))) (sub (extract v_9650 16 32) (extract v_9650 0 16))) (sub (extract v_9650 48 64) (extract v_9650 32 48))) (sub (extract v_9650 80 96) (extract v_9650 64 80))) (sub (extract v_9650 112 128) (extract v_9650 96 112)));
      pure ()
    pat_end;
    pattern fun (v_3293 : reg (bv 256)) (v_3294 : reg (bv 256)) (v_3295 : reg (bv 256)) => do
      v_9673 <- getRegister v_3293;
      v_9689 <- getRegister v_3294;
      setRegister (lhs.of_reg v_3295) (concat (concat (concat (concat (concat (concat (concat (concat (sub (extract v_9673 16 32) (extract v_9673 0 16)) (sub (extract v_9673 48 64) (extract v_9673 32 48))) (sub (extract v_9673 80 96) (extract v_9673 64 80))) (sub (extract v_9673 112 128) (extract v_9673 96 112))) (sub (extract v_9689 16 32) (extract v_9689 0 16))) (sub (extract v_9689 48 64) (extract v_9689 32 48))) (sub (extract v_9689 80 96) (extract v_9689 64 80))) (sub (extract v_9689 112 128) (extract v_9689 96 112))) (concat (concat (concat (concat (concat (concat (concat (sub (extract v_9673 144 160) (extract v_9673 128 144)) (sub (extract v_9673 176 192) (extract v_9673 160 176))) (sub (extract v_9673 208 224) (extract v_9673 192 208))) (sub (extract v_9673 240 256) (extract v_9673 224 240))) (sub (extract v_9689 144 160) (extract v_9689 128 144))) (sub (extract v_9689 176 192) (extract v_9689 160 176))) (sub (extract v_9689 208 224) (extract v_9689 192 208))) (sub (extract v_9689 240 256) (extract v_9689 224 240))));
      pure ()
    pat_end;
    pattern fun (v_3278 : Mem) (v_3274 : reg (bv 128)) (v_3275 : reg (bv 128)) => do
      v_18253 <- evaluateAddress v_3278;
      v_18254 <- load v_18253 16;
      v_18270 <- getRegister v_3274;
      setRegister (lhs.of_reg v_3275) (concat (concat (concat (concat (concat (concat (concat (sub (extract v_18254 16 32) (extract v_18254 0 16)) (sub (extract v_18254 48 64) (extract v_18254 32 48))) (sub (extract v_18254 80 96) (extract v_18254 64 80))) (sub (extract v_18254 112 128) (extract v_18254 96 112))) (sub (extract v_18270 16 32) (extract v_18270 0 16))) (sub (extract v_18270 48 64) (extract v_18270 32 48))) (sub (extract v_18270 80 96) (extract v_18270 64 80))) (sub (extract v_18270 112 128) (extract v_18270 96 112)));
      pure ()
    pat_end;
    pattern fun (v_3287 : Mem) (v_3288 : reg (bv 256)) (v_3289 : reg (bv 256)) => do
      v_18288 <- evaluateAddress v_3287;
      v_18289 <- load v_18288 32;
      v_18305 <- getRegister v_3288;
      setRegister (lhs.of_reg v_3289) (concat (concat (concat (concat (concat (concat (concat (concat (sub (extract v_18289 16 32) (extract v_18289 0 16)) (sub (extract v_18289 48 64) (extract v_18289 32 48))) (sub (extract v_18289 80 96) (extract v_18289 64 80))) (sub (extract v_18289 112 128) (extract v_18289 96 112))) (sub (extract v_18305 16 32) (extract v_18305 0 16))) (sub (extract v_18305 48 64) (extract v_18305 32 48))) (sub (extract v_18305 80 96) (extract v_18305 64 80))) (sub (extract v_18305 112 128) (extract v_18305 96 112))) (concat (concat (concat (concat (concat (concat (concat (sub (extract v_18289 144 160) (extract v_18289 128 144)) (sub (extract v_18289 176 192) (extract v_18289 160 176))) (sub (extract v_18289 208 224) (extract v_18289 192 208))) (sub (extract v_18289 240 256) (extract v_18289 224 240))) (sub (extract v_18305 144 160) (extract v_18305 128 144))) (sub (extract v_18305 176 192) (extract v_18305 160 176))) (sub (extract v_18305 208 224) (extract v_18305 192 208))) (sub (extract v_18305 240 256) (extract v_18305 224 240))));
      pure ()
    pat_end
