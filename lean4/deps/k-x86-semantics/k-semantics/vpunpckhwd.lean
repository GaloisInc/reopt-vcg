def vpunpckhwd1 : instruction :=
  definst "vpunpckhwd" $ do
    pattern fun (v_2656 : reg (bv 128)) (v_2657 : reg (bv 128)) (v_2658 : reg (bv 128)) => do
      v_6194 <- getRegister v_2656;
      v_6196 <- getRegister v_2657;
      setRegister (lhs.of_reg v_2658) (concat (concat (extract v_6194 0 16) (extract v_6196 0 16)) (concat (concat (extract v_6194 16 32) (extract v_6196 16 32)) (concat (concat (extract v_6194 32 48) (extract v_6196 32 48)) (concat (extract v_6194 48 64) (extract v_6196 48 64)))));
      pure ()
    pat_end;
    pattern fun (v_2667 : reg (bv 256)) (v_2668 : reg (bv 256)) (v_2669 : reg (bv 256)) => do
      v_6217 <- getRegister v_2667;
      v_6219 <- getRegister v_2668;
      setRegister (lhs.of_reg v_2669) (concat (concat (extract v_6217 0 16) (extract v_6219 0 16)) (concat (concat (extract v_6217 16 32) (extract v_6219 16 32)) (concat (concat (extract v_6217 32 48) (extract v_6219 32 48)) (concat (concat (extract v_6217 48 64) (extract v_6219 48 64)) (concat (concat (extract v_6217 128 144) (extract v_6219 128 144)) (concat (concat (extract v_6217 144 160) (extract v_6219 144 160)) (concat (concat (extract v_6217 160 176) (extract v_6219 160 176)) (concat (extract v_6217 176 192) (extract v_6219 176 192)))))))));
      pure ()
    pat_end;
    pattern fun (v_2651 : Mem) (v_2652 : reg (bv 128)) (v_2653 : reg (bv 128)) => do
      v_12633 <- evaluateAddress v_2651;
      v_12634 <- load v_12633 16;
      v_12636 <- getRegister v_2652;
      setRegister (lhs.of_reg v_2653) (concat (concat (extract v_12634 0 16) (extract v_12636 0 16)) (concat (concat (extract v_12634 16 32) (extract v_12636 16 32)) (concat (concat (extract v_12634 32 48) (extract v_12636 32 48)) (concat (extract v_12634 48 64) (extract v_12636 48 64)))));
      pure ()
    pat_end;
    pattern fun (v_2662 : Mem) (v_2663 : reg (bv 256)) (v_2664 : reg (bv 256)) => do
      v_12652 <- evaluateAddress v_2662;
      v_12653 <- load v_12652 32;
      v_12655 <- getRegister v_2663;
      setRegister (lhs.of_reg v_2664) (concat (concat (extract v_12653 0 16) (extract v_12655 0 16)) (concat (concat (extract v_12653 16 32) (extract v_12655 16 32)) (concat (concat (extract v_12653 32 48) (extract v_12655 32 48)) (concat (concat (extract v_12653 48 64) (extract v_12655 48 64)) (concat (concat (extract v_12653 128 144) (extract v_12655 128 144)) (concat (concat (extract v_12653 144 160) (extract v_12655 144 160)) (concat (concat (extract v_12653 160 176) (extract v_12655 160 176)) (concat (extract v_12653 176 192) (extract v_12655 176 192)))))))));
      pure ()
    pat_end
