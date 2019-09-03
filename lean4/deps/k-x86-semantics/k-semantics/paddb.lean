def paddb1 : instruction :=
  definst "paddb" $ do
    pattern fun (v_3123 : reg (bv 128)) (v_3124 : reg (bv 128)) => do
      v_5705 <- getRegister v_3124;
      v_5707 <- getRegister v_3123;
      setRegister (lhs.of_reg v_3124) (concat (add (extract v_5705 0 8) (extract v_5707 0 8)) (concat (add (extract v_5705 8 16) (extract v_5707 8 16)) (concat (add (extract v_5705 16 24) (extract v_5707 16 24)) (concat (add (extract v_5705 24 32) (extract v_5707 24 32)) (concat (add (extract v_5705 32 40) (extract v_5707 32 40)) (concat (add (extract v_5705 40 48) (extract v_5707 40 48)) (concat (add (extract v_5705 48 56) (extract v_5707 48 56)) (concat (add (extract v_5705 56 64) (extract v_5707 56 64)) (concat (add (extract v_5705 64 72) (extract v_5707 64 72)) (concat (add (extract v_5705 72 80) (extract v_5707 72 80)) (concat (add (extract v_5705 80 88) (extract v_5707 80 88)) (concat (add (extract v_5705 88 96) (extract v_5707 88 96)) (concat (add (extract v_5705 96 104) (extract v_5707 96 104)) (concat (add (extract v_5705 104 112) (extract v_5707 104 112)) (concat (add (extract v_5705 112 120) (extract v_5707 112 120)) (add (extract v_5705 120 128) (extract v_5707 120 128)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3119 : Mem) (v_3120 : reg (bv 128)) => do
      v_9789 <- getRegister v_3120;
      v_9791 <- evaluateAddress v_3119;
      v_9792 <- load v_9791 16;
      setRegister (lhs.of_reg v_3120) (concat (add (extract v_9789 0 8) (extract v_9792 0 8)) (concat (add (extract v_9789 8 16) (extract v_9792 8 16)) (concat (add (extract v_9789 16 24) (extract v_9792 16 24)) (concat (add (extract v_9789 24 32) (extract v_9792 24 32)) (concat (add (extract v_9789 32 40) (extract v_9792 32 40)) (concat (add (extract v_9789 40 48) (extract v_9792 40 48)) (concat (add (extract v_9789 48 56) (extract v_9792 48 56)) (concat (add (extract v_9789 56 64) (extract v_9792 56 64)) (concat (add (extract v_9789 64 72) (extract v_9792 64 72)) (concat (add (extract v_9789 72 80) (extract v_9792 72 80)) (concat (add (extract v_9789 80 88) (extract v_9792 80 88)) (concat (add (extract v_9789 88 96) (extract v_9792 88 96)) (concat (add (extract v_9789 96 104) (extract v_9792 96 104)) (concat (add (extract v_9789 104 112) (extract v_9792 104 112)) (concat (add (extract v_9789 112 120) (extract v_9792 112 120)) (add (extract v_9789 120 128) (extract v_9792 120 128)))))))))))))))));
      pure ()
    pat_end
