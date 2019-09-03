def vpaddw1 : instruction :=
  definst "vpaddw" $ do
    pattern fun (v_2474 : reg (bv 128)) (v_2475 : reg (bv 128)) (v_2476 : reg (bv 128)) => do
      v_5711 <- getRegister v_2475;
      v_5713 <- getRegister v_2474;
      setRegister (lhs.of_reg v_2476) (concat (add (extract v_5711 0 16) (extract v_5713 0 16)) (concat (add (extract v_5711 16 32) (extract v_5713 16 32)) (concat (add (extract v_5711 32 48) (extract v_5713 32 48)) (concat (add (extract v_5711 48 64) (extract v_5713 48 64)) (concat (add (extract v_5711 64 80) (extract v_5713 64 80)) (concat (add (extract v_5711 80 96) (extract v_5713 80 96)) (concat (add (extract v_5711 96 112) (extract v_5713 96 112)) (add (extract v_5711 112 128) (extract v_5713 112 128)))))))));
      pure ()
    pat_end;
    pattern fun (v_2485 : reg (bv 256)) (v_2486 : reg (bv 256)) (v_2487 : reg (bv 256)) => do
      v_5750 <- getRegister v_2486;
      v_5752 <- getRegister v_2485;
      setRegister (lhs.of_reg v_2487) (concat (add (extract v_5750 0 16) (extract v_5752 0 16)) (concat (add (extract v_5750 16 32) (extract v_5752 16 32)) (concat (add (extract v_5750 32 48) (extract v_5752 32 48)) (concat (add (extract v_5750 48 64) (extract v_5752 48 64)) (concat (add (extract v_5750 64 80) (extract v_5752 64 80)) (concat (add (extract v_5750 80 96) (extract v_5752 80 96)) (concat (add (extract v_5750 96 112) (extract v_5752 96 112)) (concat (add (extract v_5750 112 128) (extract v_5752 112 128)) (concat (add (extract v_5750 128 144) (extract v_5752 128 144)) (concat (add (extract v_5750 144 160) (extract v_5752 144 160)) (concat (add (extract v_5750 160 176) (extract v_5752 160 176)) (concat (add (extract v_5750 176 192) (extract v_5752 176 192)) (concat (add (extract v_5750 192 208) (extract v_5752 192 208)) (concat (add (extract v_5750 208 224) (extract v_5752 208 224)) (concat (add (extract v_5750 224 240) (extract v_5752 224 240)) (add (extract v_5750 240 256) (extract v_5752 240 256)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2468 : Mem) (v_2469 : reg (bv 128)) (v_2470 : reg (bv 128)) => do
      v_15059 <- getRegister v_2469;
      v_15061 <- evaluateAddress v_2468;
      v_15062 <- load v_15061 16;
      setRegister (lhs.of_reg v_2470) (concat (add (extract v_15059 0 16) (extract v_15062 0 16)) (concat (add (extract v_15059 16 32) (extract v_15062 16 32)) (concat (add (extract v_15059 32 48) (extract v_15062 32 48)) (concat (add (extract v_15059 48 64) (extract v_15062 48 64)) (concat (add (extract v_15059 64 80) (extract v_15062 64 80)) (concat (add (extract v_15059 80 96) (extract v_15062 80 96)) (concat (add (extract v_15059 96 112) (extract v_15062 96 112)) (add (extract v_15059 112 128) (extract v_15062 112 128)))))))));
      pure ()
    pat_end;
    pattern fun (v_2479 : Mem) (v_2480 : reg (bv 256)) (v_2481 : reg (bv 256)) => do
      v_15094 <- getRegister v_2480;
      v_15096 <- evaluateAddress v_2479;
      v_15097 <- load v_15096 32;
      setRegister (lhs.of_reg v_2481) (concat (add (extract v_15094 0 16) (extract v_15097 0 16)) (concat (add (extract v_15094 16 32) (extract v_15097 16 32)) (concat (add (extract v_15094 32 48) (extract v_15097 32 48)) (concat (add (extract v_15094 48 64) (extract v_15097 48 64)) (concat (add (extract v_15094 64 80) (extract v_15097 64 80)) (concat (add (extract v_15094 80 96) (extract v_15097 80 96)) (concat (add (extract v_15094 96 112) (extract v_15097 96 112)) (concat (add (extract v_15094 112 128) (extract v_15097 112 128)) (concat (add (extract v_15094 128 144) (extract v_15097 128 144)) (concat (add (extract v_15094 144 160) (extract v_15097 144 160)) (concat (add (extract v_15094 160 176) (extract v_15097 160 176)) (concat (add (extract v_15094 176 192) (extract v_15097 176 192)) (concat (add (extract v_15094 192 208) (extract v_15097 192 208)) (concat (add (extract v_15094 208 224) (extract v_15097 208 224)) (concat (add (extract v_15094 224 240) (extract v_15097 224 240)) (add (extract v_15094 240 256) (extract v_15097 240 256)))))))))))))))));
      pure ()
    pat_end
