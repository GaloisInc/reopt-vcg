def vpunpckhbw1 : instruction :=
  definst "vpunpckhbw" $ do
    pattern fun (v_2590 : reg (bv 128)) (v_2591 : reg (bv 128)) (v_2592 : reg (bv 128)) => do
      v_6020 <- getRegister v_2590;
      v_6022 <- getRegister v_2591;
      setRegister (lhs.of_reg v_2592) (concat (concat (extract v_6020 0 8) (extract v_6022 0 8)) (concat (concat (extract v_6020 8 16) (extract v_6022 8 16)) (concat (concat (extract v_6020 16 24) (extract v_6022 16 24)) (concat (concat (extract v_6020 24 32) (extract v_6022 24 32)) (concat (concat (extract v_6020 32 40) (extract v_6022 32 40)) (concat (concat (extract v_6020 40 48) (extract v_6022 40 48)) (concat (concat (extract v_6020 48 56) (extract v_6022 48 56)) (concat (extract v_6020 56 64) (extract v_6022 56 64)))))))));
      pure ()
    pat_end;
    pattern fun (v_2601 : reg (bv 256)) (v_2602 : reg (bv 256)) (v_2603 : reg (bv 256)) => do
      v_6059 <- getRegister v_2601;
      v_6061 <- getRegister v_2602;
      setRegister (lhs.of_reg v_2603) (concat (concat (extract v_6059 0 8) (extract v_6061 0 8)) (concat (concat (extract v_6059 8 16) (extract v_6061 8 16)) (concat (concat (extract v_6059 16 24) (extract v_6061 16 24)) (concat (concat (extract v_6059 24 32) (extract v_6061 24 32)) (concat (concat (extract v_6059 32 40) (extract v_6061 32 40)) (concat (concat (extract v_6059 40 48) (extract v_6061 40 48)) (concat (concat (extract v_6059 48 56) (extract v_6061 48 56)) (concat (concat (extract v_6059 56 64) (extract v_6061 56 64)) (concat (concat (extract v_6059 128 136) (extract v_6061 128 136)) (concat (concat (extract v_6059 136 144) (extract v_6061 136 144)) (concat (concat (extract v_6059 144 152) (extract v_6061 144 152)) (concat (concat (extract v_6059 152 160) (extract v_6061 152 160)) (concat (concat (extract v_6059 160 168) (extract v_6061 160 168)) (concat (concat (extract v_6059 168 176) (extract v_6061 168 176)) (concat (concat (extract v_6059 176 184) (extract v_6061 176 184)) (concat (extract v_6059 184 192) (extract v_6061 184 192)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2585 : Mem) (v_2586 : reg (bv 128)) (v_2587 : reg (bv 128)) => do
      v_12483 <- evaluateAddress v_2585;
      v_12484 <- load v_12483 16;
      v_12486 <- getRegister v_2586;
      setRegister (lhs.of_reg v_2587) (concat (concat (extract v_12484 0 8) (extract v_12486 0 8)) (concat (concat (extract v_12484 8 16) (extract v_12486 8 16)) (concat (concat (extract v_12484 16 24) (extract v_12486 16 24)) (concat (concat (extract v_12484 24 32) (extract v_12486 24 32)) (concat (concat (extract v_12484 32 40) (extract v_12486 32 40)) (concat (concat (extract v_12484 40 48) (extract v_12486 40 48)) (concat (concat (extract v_12484 48 56) (extract v_12486 48 56)) (concat (extract v_12484 56 64) (extract v_12486 56 64)))))))));
      pure ()
    pat_end;
    pattern fun (v_2596 : Mem) (v_2597 : reg (bv 256)) (v_2598 : reg (bv 256)) => do
      v_12518 <- evaluateAddress v_2596;
      v_12519 <- load v_12518 32;
      v_12521 <- getRegister v_2597;
      setRegister (lhs.of_reg v_2598) (concat (concat (extract v_12519 0 8) (extract v_12521 0 8)) (concat (concat (extract v_12519 8 16) (extract v_12521 8 16)) (concat (concat (extract v_12519 16 24) (extract v_12521 16 24)) (concat (concat (extract v_12519 24 32) (extract v_12521 24 32)) (concat (concat (extract v_12519 32 40) (extract v_12521 32 40)) (concat (concat (extract v_12519 40 48) (extract v_12521 40 48)) (concat (concat (extract v_12519 48 56) (extract v_12521 48 56)) (concat (concat (extract v_12519 56 64) (extract v_12521 56 64)) (concat (concat (extract v_12519 128 136) (extract v_12521 128 136)) (concat (concat (extract v_12519 136 144) (extract v_12521 136 144)) (concat (concat (extract v_12519 144 152) (extract v_12521 144 152)) (concat (concat (extract v_12519 152 160) (extract v_12521 152 160)) (concat (concat (extract v_12519 160 168) (extract v_12521 160 168)) (concat (concat (extract v_12519 168 176) (extract v_12521 168 176)) (concat (concat (extract v_12519 176 184) (extract v_12521 176 184)) (concat (extract v_12519 184 192) (extract v_12521 184 192)))))))))))))))));
      pure ()
    pat_end
