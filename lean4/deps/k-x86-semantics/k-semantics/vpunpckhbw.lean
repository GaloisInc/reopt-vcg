def vpunpckhbw1 : instruction :=
  definst "vpunpckhbw" $ do
    pattern fun (v_2671 : reg (bv 128)) (v_2672 : reg (bv 128)) (v_2673 : reg (bv 128)) => do
      v_6096 <- getRegister v_2671;
      v_6098 <- getRegister v_2672;
      setRegister (lhs.of_reg v_2673) (concat (concat (extract v_6096 0 8) (extract v_6098 0 8)) (concat (concat (extract v_6096 8 16) (extract v_6098 8 16)) (concat (concat (extract v_6096 16 24) (extract v_6098 16 24)) (concat (concat (extract v_6096 24 32) (extract v_6098 24 32)) (concat (concat (extract v_6096 32 40) (extract v_6098 32 40)) (concat (concat (extract v_6096 40 48) (extract v_6098 40 48)) (concat (concat (extract v_6096 48 56) (extract v_6098 48 56)) (concat (extract v_6096 56 64) (extract v_6098 56 64)))))))));
      pure ()
    pat_end;
    pattern fun (v_2682 : reg (bv 256)) (v_2683 : reg (bv 256)) (v_2684 : reg (bv 256)) => do
      v_6135 <- getRegister v_2682;
      v_6137 <- getRegister v_2683;
      setRegister (lhs.of_reg v_2684) (concat (concat (extract v_6135 0 8) (extract v_6137 0 8)) (concat (concat (extract v_6135 8 16) (extract v_6137 8 16)) (concat (concat (extract v_6135 16 24) (extract v_6137 16 24)) (concat (concat (extract v_6135 24 32) (extract v_6137 24 32)) (concat (concat (extract v_6135 32 40) (extract v_6137 32 40)) (concat (concat (extract v_6135 40 48) (extract v_6137 40 48)) (concat (concat (extract v_6135 48 56) (extract v_6137 48 56)) (concat (concat (extract v_6135 56 64) (extract v_6137 56 64)) (concat (concat (extract v_6135 128 136) (extract v_6137 128 136)) (concat (concat (extract v_6135 136 144) (extract v_6137 136 144)) (concat (concat (extract v_6135 144 152) (extract v_6137 144 152)) (concat (concat (extract v_6135 152 160) (extract v_6137 152 160)) (concat (concat (extract v_6135 160 168) (extract v_6137 160 168)) (concat (concat (extract v_6135 168 176) (extract v_6137 168 176)) (concat (concat (extract v_6135 176 184) (extract v_6137 176 184)) (concat (extract v_6135 184 192) (extract v_6137 184 192)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2665 : Mem) (v_2666 : reg (bv 128)) (v_2667 : reg (bv 128)) => do
      v_12186 <- evaluateAddress v_2665;
      v_12187 <- load v_12186 16;
      v_12189 <- getRegister v_2666;
      setRegister (lhs.of_reg v_2667) (concat (concat (extract v_12187 0 8) (extract v_12189 0 8)) (concat (concat (extract v_12187 8 16) (extract v_12189 8 16)) (concat (concat (extract v_12187 16 24) (extract v_12189 16 24)) (concat (concat (extract v_12187 24 32) (extract v_12189 24 32)) (concat (concat (extract v_12187 32 40) (extract v_12189 32 40)) (concat (concat (extract v_12187 40 48) (extract v_12189 40 48)) (concat (concat (extract v_12187 48 56) (extract v_12189 48 56)) (concat (extract v_12187 56 64) (extract v_12189 56 64)))))))));
      pure ()
    pat_end;
    pattern fun (v_2676 : Mem) (v_2677 : reg (bv 256)) (v_2678 : reg (bv 256)) => do
      v_12221 <- evaluateAddress v_2676;
      v_12222 <- load v_12221 32;
      v_12224 <- getRegister v_2677;
      setRegister (lhs.of_reg v_2678) (concat (concat (extract v_12222 0 8) (extract v_12224 0 8)) (concat (concat (extract v_12222 8 16) (extract v_12224 8 16)) (concat (concat (extract v_12222 16 24) (extract v_12224 16 24)) (concat (concat (extract v_12222 24 32) (extract v_12224 24 32)) (concat (concat (extract v_12222 32 40) (extract v_12224 32 40)) (concat (concat (extract v_12222 40 48) (extract v_12224 40 48)) (concat (concat (extract v_12222 48 56) (extract v_12224 48 56)) (concat (concat (extract v_12222 56 64) (extract v_12224 56 64)) (concat (concat (extract v_12222 128 136) (extract v_12224 128 136)) (concat (concat (extract v_12222 136 144) (extract v_12224 136 144)) (concat (concat (extract v_12222 144 152) (extract v_12224 144 152)) (concat (concat (extract v_12222 152 160) (extract v_12224 152 160)) (concat (concat (extract v_12222 160 168) (extract v_12224 160 168)) (concat (concat (extract v_12222 168 176) (extract v_12224 168 176)) (concat (concat (extract v_12222 176 184) (extract v_12224 176 184)) (concat (extract v_12222 184 192) (extract v_12224 184 192)))))))))))))))));
      pure ()
    pat_end
