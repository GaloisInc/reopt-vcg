def vpaddw1 : instruction :=
  definst "vpaddw" $ do
    pattern fun (v_2564 : reg (bv 128)) (v_2565 : reg (bv 128)) (v_2566 : reg (bv 128)) => do
      v_5586 <- getRegister v_2565;
      v_5588 <- getRegister v_2564;
      setRegister (lhs.of_reg v_2566) (concat (add (extract v_5586 0 16) (extract v_5588 0 16)) (concat (add (extract v_5586 16 32) (extract v_5588 16 32)) (concat (add (extract v_5586 32 48) (extract v_5588 32 48)) (concat (add (extract v_5586 48 64) (extract v_5588 48 64)) (concat (add (extract v_5586 64 80) (extract v_5588 64 80)) (concat (add (extract v_5586 80 96) (extract v_5588 80 96)) (concat (add (extract v_5586 96 112) (extract v_5588 96 112)) (add (extract v_5586 112 128) (extract v_5588 112 128)))))))));
      pure ()
    pat_end;
    pattern fun (v_2575 : reg (bv 256)) (v_2576 : reg (bv 256)) (v_2577 : reg (bv 256)) => do
      v_5625 <- getRegister v_2576;
      v_5627 <- getRegister v_2575;
      setRegister (lhs.of_reg v_2577) (concat (add (extract v_5625 0 16) (extract v_5627 0 16)) (concat (add (extract v_5625 16 32) (extract v_5627 16 32)) (concat (add (extract v_5625 32 48) (extract v_5627 32 48)) (concat (add (extract v_5625 48 64) (extract v_5627 48 64)) (concat (add (extract v_5625 64 80) (extract v_5627 64 80)) (concat (add (extract v_5625 80 96) (extract v_5627 80 96)) (concat (add (extract v_5625 96 112) (extract v_5627 96 112)) (concat (add (extract v_5625 112 128) (extract v_5627 112 128)) (concat (add (extract v_5625 128 144) (extract v_5627 128 144)) (concat (add (extract v_5625 144 160) (extract v_5627 144 160)) (concat (add (extract v_5625 160 176) (extract v_5627 160 176)) (concat (add (extract v_5625 176 192) (extract v_5627 176 192)) (concat (add (extract v_5625 192 208) (extract v_5627 192 208)) (concat (add (extract v_5625 208 224) (extract v_5627 208 224)) (concat (add (extract v_5625 224 240) (extract v_5627 224 240)) (add (extract v_5625 240 256) (extract v_5627 240 256)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2559 : Mem) (v_2560 : reg (bv 128)) (v_2561 : reg (bv 128)) => do
      v_14314 <- getRegister v_2560;
      v_14316 <- evaluateAddress v_2559;
      v_14317 <- load v_14316 16;
      setRegister (lhs.of_reg v_2561) (concat (add (extract v_14314 0 16) (extract v_14317 0 16)) (concat (add (extract v_14314 16 32) (extract v_14317 16 32)) (concat (add (extract v_14314 32 48) (extract v_14317 32 48)) (concat (add (extract v_14314 48 64) (extract v_14317 48 64)) (concat (add (extract v_14314 64 80) (extract v_14317 64 80)) (concat (add (extract v_14314 80 96) (extract v_14317 80 96)) (concat (add (extract v_14314 96 112) (extract v_14317 96 112)) (add (extract v_14314 112 128) (extract v_14317 112 128)))))))));
      pure ()
    pat_end;
    pattern fun (v_2570 : Mem) (v_2571 : reg (bv 256)) (v_2572 : reg (bv 256)) => do
      v_14349 <- getRegister v_2571;
      v_14351 <- evaluateAddress v_2570;
      v_14352 <- load v_14351 32;
      setRegister (lhs.of_reg v_2572) (concat (add (extract v_14349 0 16) (extract v_14352 0 16)) (concat (add (extract v_14349 16 32) (extract v_14352 16 32)) (concat (add (extract v_14349 32 48) (extract v_14352 32 48)) (concat (add (extract v_14349 48 64) (extract v_14352 48 64)) (concat (add (extract v_14349 64 80) (extract v_14352 64 80)) (concat (add (extract v_14349 80 96) (extract v_14352 80 96)) (concat (add (extract v_14349 96 112) (extract v_14352 96 112)) (concat (add (extract v_14349 112 128) (extract v_14352 112 128)) (concat (add (extract v_14349 128 144) (extract v_14352 128 144)) (concat (add (extract v_14349 144 160) (extract v_14352 144 160)) (concat (add (extract v_14349 160 176) (extract v_14352 160 176)) (concat (add (extract v_14349 176 192) (extract v_14352 176 192)) (concat (add (extract v_14349 192 208) (extract v_14352 192 208)) (concat (add (extract v_14349 208 224) (extract v_14352 208 224)) (concat (add (extract v_14349 224 240) (extract v_14352 224 240)) (add (extract v_14349 240 256) (extract v_14352 240 256)))))))))))))))));
      pure ()
    pat_end
