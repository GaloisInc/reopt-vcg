def vpaddw1 : instruction :=
  definst "vpaddw" $ do
    pattern fun (v_2484 : reg (bv 128)) (v_2485 : reg (bv 128)) (v_2486 : reg (bv 128)) => do
      v_5580 <- getRegister v_2485;
      v_5582 <- getRegister v_2484;
      setRegister (lhs.of_reg v_2486) (concat (add (extract v_5580 0 16) (extract v_5582 0 16)) (concat (add (extract v_5580 16 32) (extract v_5582 16 32)) (concat (add (extract v_5580 32 48) (extract v_5582 32 48)) (concat (add (extract v_5580 48 64) (extract v_5582 48 64)) (concat (add (extract v_5580 64 80) (extract v_5582 64 80)) (concat (add (extract v_5580 80 96) (extract v_5582 80 96)) (concat (add (extract v_5580 96 112) (extract v_5582 96 112)) (add (extract v_5580 112 128) (extract v_5582 112 128)))))))));
      pure ()
    pat_end;
    pattern fun (v_2498 : reg (bv 256)) (v_2499 : reg (bv 256)) (v_2500 : reg (bv 256)) => do
      v_5619 <- getRegister v_2499;
      v_5621 <- getRegister v_2498;
      setRegister (lhs.of_reg v_2500) (concat (add (extract v_5619 0 16) (extract v_5621 0 16)) (concat (add (extract v_5619 16 32) (extract v_5621 16 32)) (concat (add (extract v_5619 32 48) (extract v_5621 32 48)) (concat (add (extract v_5619 48 64) (extract v_5621 48 64)) (concat (add (extract v_5619 64 80) (extract v_5621 64 80)) (concat (add (extract v_5619 80 96) (extract v_5621 80 96)) (concat (add (extract v_5619 96 112) (extract v_5621 96 112)) (concat (add (extract v_5619 112 128) (extract v_5621 112 128)) (concat (add (extract v_5619 128 144) (extract v_5621 128 144)) (concat (add (extract v_5619 144 160) (extract v_5621 144 160)) (concat (add (extract v_5619 160 176) (extract v_5621 160 176)) (concat (add (extract v_5619 176 192) (extract v_5621 176 192)) (concat (add (extract v_5619 192 208) (extract v_5621 192 208)) (concat (add (extract v_5619 208 224) (extract v_5621 208 224)) (concat (add (extract v_5619 224 240) (extract v_5621 224 240)) (add (extract v_5619 240 256) (extract v_5621 240 256)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2483 : Mem) (v_2479 : reg (bv 128)) (v_2480 : reg (bv 128)) => do
      v_14556 <- getRegister v_2479;
      v_14558 <- evaluateAddress v_2483;
      v_14559 <- load v_14558 16;
      setRegister (lhs.of_reg v_2480) (concat (add (extract v_14556 0 16) (extract v_14559 0 16)) (concat (add (extract v_14556 16 32) (extract v_14559 16 32)) (concat (add (extract v_14556 32 48) (extract v_14559 32 48)) (concat (add (extract v_14556 48 64) (extract v_14559 48 64)) (concat (add (extract v_14556 64 80) (extract v_14559 64 80)) (concat (add (extract v_14556 80 96) (extract v_14559 80 96)) (concat (add (extract v_14556 96 112) (extract v_14559 96 112)) (add (extract v_14556 112 128) (extract v_14559 112 128)))))))));
      pure ()
    pat_end;
    pattern fun (v_2492 : Mem) (v_2493 : reg (bv 256)) (v_2494 : reg (bv 256)) => do
      v_14591 <- getRegister v_2493;
      v_14593 <- evaluateAddress v_2492;
      v_14594 <- load v_14593 32;
      setRegister (lhs.of_reg v_2494) (concat (add (extract v_14591 0 16) (extract v_14594 0 16)) (concat (add (extract v_14591 16 32) (extract v_14594 16 32)) (concat (add (extract v_14591 32 48) (extract v_14594 32 48)) (concat (add (extract v_14591 48 64) (extract v_14594 48 64)) (concat (add (extract v_14591 64 80) (extract v_14594 64 80)) (concat (add (extract v_14591 80 96) (extract v_14594 80 96)) (concat (add (extract v_14591 96 112) (extract v_14594 96 112)) (concat (add (extract v_14591 112 128) (extract v_14594 112 128)) (concat (add (extract v_14591 128 144) (extract v_14594 128 144)) (concat (add (extract v_14591 144 160) (extract v_14594 144 160)) (concat (add (extract v_14591 160 176) (extract v_14594 160 176)) (concat (add (extract v_14591 176 192) (extract v_14594 176 192)) (concat (add (extract v_14591 192 208) (extract v_14594 192 208)) (concat (add (extract v_14591 208 224) (extract v_14594 208 224)) (concat (add (extract v_14591 224 240) (extract v_14594 224 240)) (add (extract v_14591 240 256) (extract v_14594 240 256)))))))))))))))));
      pure ()
    pat_end
