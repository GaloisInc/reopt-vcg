def vpunpckhbw1 : instruction :=
  definst "vpunpckhbw" $ do
    pattern fun (v_2644 : reg (bv 128)) (v_2645 : reg (bv 128)) (v_2646 : reg (bv 128)) => do
      v_6069 <- getRegister v_2644;
      v_6071 <- getRegister v_2645;
      setRegister (lhs.of_reg v_2646) (concat (concat (extract v_6069 0 8) (extract v_6071 0 8)) (concat (concat (extract v_6069 8 16) (extract v_6071 8 16)) (concat (concat (extract v_6069 16 24) (extract v_6071 16 24)) (concat (concat (extract v_6069 24 32) (extract v_6071 24 32)) (concat (concat (extract v_6069 32 40) (extract v_6071 32 40)) (concat (concat (extract v_6069 40 48) (extract v_6071 40 48)) (concat (concat (extract v_6069 48 56) (extract v_6071 48 56)) (concat (extract v_6069 56 64) (extract v_6071 56 64)))))))));
      pure ()
    pat_end;
    pattern fun (v_2655 : reg (bv 256)) (v_2656 : reg (bv 256)) (v_2657 : reg (bv 256)) => do
      v_6108 <- getRegister v_2655;
      v_6110 <- getRegister v_2656;
      setRegister (lhs.of_reg v_2657) (concat (concat (extract v_6108 0 8) (extract v_6110 0 8)) (concat (concat (extract v_6108 8 16) (extract v_6110 8 16)) (concat (concat (extract v_6108 16 24) (extract v_6110 16 24)) (concat (concat (extract v_6108 24 32) (extract v_6110 24 32)) (concat (concat (extract v_6108 32 40) (extract v_6110 32 40)) (concat (concat (extract v_6108 40 48) (extract v_6110 40 48)) (concat (concat (extract v_6108 48 56) (extract v_6110 48 56)) (concat (concat (extract v_6108 56 64) (extract v_6110 56 64)) (concat (concat (extract v_6108 128 136) (extract v_6110 128 136)) (concat (concat (extract v_6108 136 144) (extract v_6110 136 144)) (concat (concat (extract v_6108 144 152) (extract v_6110 144 152)) (concat (concat (extract v_6108 152 160) (extract v_6110 152 160)) (concat (concat (extract v_6108 160 168) (extract v_6110 160 168)) (concat (concat (extract v_6108 168 176) (extract v_6110 168 176)) (concat (concat (extract v_6108 176 184) (extract v_6110 176 184)) (concat (extract v_6108 184 192) (extract v_6110 184 192)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2638 : Mem) (v_2639 : reg (bv 128)) (v_2640 : reg (bv 128)) => do
      v_12159 <- evaluateAddress v_2638;
      v_12160 <- load v_12159 16;
      v_12162 <- getRegister v_2639;
      setRegister (lhs.of_reg v_2640) (concat (concat (extract v_12160 0 8) (extract v_12162 0 8)) (concat (concat (extract v_12160 8 16) (extract v_12162 8 16)) (concat (concat (extract v_12160 16 24) (extract v_12162 16 24)) (concat (concat (extract v_12160 24 32) (extract v_12162 24 32)) (concat (concat (extract v_12160 32 40) (extract v_12162 32 40)) (concat (concat (extract v_12160 40 48) (extract v_12162 40 48)) (concat (concat (extract v_12160 48 56) (extract v_12162 48 56)) (concat (extract v_12160 56 64) (extract v_12162 56 64)))))))));
      pure ()
    pat_end;
    pattern fun (v_2649 : Mem) (v_2650 : reg (bv 256)) (v_2651 : reg (bv 256)) => do
      v_12194 <- evaluateAddress v_2649;
      v_12195 <- load v_12194 32;
      v_12197 <- getRegister v_2650;
      setRegister (lhs.of_reg v_2651) (concat (concat (extract v_12195 0 8) (extract v_12197 0 8)) (concat (concat (extract v_12195 8 16) (extract v_12197 8 16)) (concat (concat (extract v_12195 16 24) (extract v_12197 16 24)) (concat (concat (extract v_12195 24 32) (extract v_12197 24 32)) (concat (concat (extract v_12195 32 40) (extract v_12197 32 40)) (concat (concat (extract v_12195 40 48) (extract v_12197 40 48)) (concat (concat (extract v_12195 48 56) (extract v_12197 48 56)) (concat (concat (extract v_12195 56 64) (extract v_12197 56 64)) (concat (concat (extract v_12195 128 136) (extract v_12197 128 136)) (concat (concat (extract v_12195 136 144) (extract v_12197 136 144)) (concat (concat (extract v_12195 144 152) (extract v_12197 144 152)) (concat (concat (extract v_12195 152 160) (extract v_12197 152 160)) (concat (concat (extract v_12195 160 168) (extract v_12197 160 168)) (concat (concat (extract v_12195 168 176) (extract v_12197 168 176)) (concat (concat (extract v_12195 176 184) (extract v_12197 176 184)) (concat (extract v_12195 184 192) (extract v_12197 184 192)))))))))))))))));
      pure ()
    pat_end
