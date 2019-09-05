def vpaddw1 : instruction :=
  definst "vpaddw" $ do
    pattern fun (v_2538 : reg (bv 128)) (v_2539 : reg (bv 128)) (v_2540 : reg (bv 128)) => do
      v_5559 <- getRegister v_2539;
      v_5561 <- getRegister v_2538;
      setRegister (lhs.of_reg v_2540) (concat (add (extract v_5559 0 16) (extract v_5561 0 16)) (concat (add (extract v_5559 16 32) (extract v_5561 16 32)) (concat (add (extract v_5559 32 48) (extract v_5561 32 48)) (concat (add (extract v_5559 48 64) (extract v_5561 48 64)) (concat (add (extract v_5559 64 80) (extract v_5561 64 80)) (concat (add (extract v_5559 80 96) (extract v_5561 80 96)) (concat (add (extract v_5559 96 112) (extract v_5561 96 112)) (add (extract v_5559 112 128) (extract v_5561 112 128)))))))));
      pure ()
    pat_end;
    pattern fun (v_2548 : reg (bv 256)) (v_2549 : reg (bv 256)) (v_2550 : reg (bv 256)) => do
      v_5598 <- getRegister v_2549;
      v_5600 <- getRegister v_2548;
      setRegister (lhs.of_reg v_2550) (concat (add (extract v_5598 0 16) (extract v_5600 0 16)) (concat (add (extract v_5598 16 32) (extract v_5600 16 32)) (concat (add (extract v_5598 32 48) (extract v_5600 32 48)) (concat (add (extract v_5598 48 64) (extract v_5600 48 64)) (concat (add (extract v_5598 64 80) (extract v_5600 64 80)) (concat (add (extract v_5598 80 96) (extract v_5600 80 96)) (concat (add (extract v_5598 96 112) (extract v_5600 96 112)) (concat (add (extract v_5598 112 128) (extract v_5600 112 128)) (concat (add (extract v_5598 128 144) (extract v_5600 128 144)) (concat (add (extract v_5598 144 160) (extract v_5600 144 160)) (concat (add (extract v_5598 160 176) (extract v_5600 160 176)) (concat (add (extract v_5598 176 192) (extract v_5600 176 192)) (concat (add (extract v_5598 192 208) (extract v_5600 192 208)) (concat (add (extract v_5598 208 224) (extract v_5600 208 224)) (concat (add (extract v_5598 224 240) (extract v_5600 224 240)) (add (extract v_5598 240 256) (extract v_5600 240 256)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2532 : Mem) (v_2533 : reg (bv 128)) (v_2534 : reg (bv 128)) => do
      v_14287 <- getRegister v_2533;
      v_14289 <- evaluateAddress v_2532;
      v_14290 <- load v_14289 16;
      setRegister (lhs.of_reg v_2534) (concat (add (extract v_14287 0 16) (extract v_14290 0 16)) (concat (add (extract v_14287 16 32) (extract v_14290 16 32)) (concat (add (extract v_14287 32 48) (extract v_14290 32 48)) (concat (add (extract v_14287 48 64) (extract v_14290 48 64)) (concat (add (extract v_14287 64 80) (extract v_14290 64 80)) (concat (add (extract v_14287 80 96) (extract v_14290 80 96)) (concat (add (extract v_14287 96 112) (extract v_14290 96 112)) (add (extract v_14287 112 128) (extract v_14290 112 128)))))))));
      pure ()
    pat_end;
    pattern fun (v_2543 : Mem) (v_2544 : reg (bv 256)) (v_2545 : reg (bv 256)) => do
      v_14322 <- getRegister v_2544;
      v_14324 <- evaluateAddress v_2543;
      v_14325 <- load v_14324 32;
      setRegister (lhs.of_reg v_2545) (concat (add (extract v_14322 0 16) (extract v_14325 0 16)) (concat (add (extract v_14322 16 32) (extract v_14325 16 32)) (concat (add (extract v_14322 32 48) (extract v_14325 32 48)) (concat (add (extract v_14322 48 64) (extract v_14325 48 64)) (concat (add (extract v_14322 64 80) (extract v_14325 64 80)) (concat (add (extract v_14322 80 96) (extract v_14325 80 96)) (concat (add (extract v_14322 96 112) (extract v_14325 96 112)) (concat (add (extract v_14322 112 128) (extract v_14325 112 128)) (concat (add (extract v_14322 128 144) (extract v_14325 128 144)) (concat (add (extract v_14322 144 160) (extract v_14325 144 160)) (concat (add (extract v_14322 160 176) (extract v_14325 160 176)) (concat (add (extract v_14322 176 192) (extract v_14325 176 192)) (concat (add (extract v_14322 192 208) (extract v_14325 192 208)) (concat (add (extract v_14322 208 224) (extract v_14325 208 224)) (concat (add (extract v_14322 224 240) (extract v_14325 224 240)) (add (extract v_14322 240 256) (extract v_14325 240 256)))))))))))))))));
      pure ()
    pat_end
