def paddb1 : instruction :=
  definst "paddb" $ do
    pattern fun (v_3111 : reg (bv 128)) (v_3112 : reg (bv 128)) => do
      v_5674 <- getRegister v_3112;
      v_5676 <- getRegister v_3111;
      setRegister (lhs.of_reg v_3112) (concat (add (extract v_5674 0 8) (extract v_5676 0 8)) (concat (add (extract v_5674 8 16) (extract v_5676 8 16)) (concat (add (extract v_5674 16 24) (extract v_5676 16 24)) (concat (add (extract v_5674 24 32) (extract v_5676 24 32)) (concat (add (extract v_5674 32 40) (extract v_5676 32 40)) (concat (add (extract v_5674 40 48) (extract v_5676 40 48)) (concat (add (extract v_5674 48 56) (extract v_5676 48 56)) (concat (add (extract v_5674 56 64) (extract v_5676 56 64)) (concat (add (extract v_5674 64 72) (extract v_5676 64 72)) (concat (add (extract v_5674 72 80) (extract v_5676 72 80)) (concat (add (extract v_5674 80 88) (extract v_5676 80 88)) (concat (add (extract v_5674 88 96) (extract v_5676 88 96)) (concat (add (extract v_5674 96 104) (extract v_5676 96 104)) (concat (add (extract v_5674 104 112) (extract v_5676 104 112)) (concat (add (extract v_5674 112 120) (extract v_5676 112 120)) (add (extract v_5674 120 128) (extract v_5676 120 128)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3106 : Mem) (v_3107 : reg (bv 128)) => do
      v_9770 <- getRegister v_3107;
      v_9772 <- evaluateAddress v_3106;
      v_9773 <- load v_9772 16;
      setRegister (lhs.of_reg v_3107) (concat (add (extract v_9770 0 8) (extract v_9773 0 8)) (concat (add (extract v_9770 8 16) (extract v_9773 8 16)) (concat (add (extract v_9770 16 24) (extract v_9773 16 24)) (concat (add (extract v_9770 24 32) (extract v_9773 24 32)) (concat (add (extract v_9770 32 40) (extract v_9773 32 40)) (concat (add (extract v_9770 40 48) (extract v_9773 40 48)) (concat (add (extract v_9770 48 56) (extract v_9773 48 56)) (concat (add (extract v_9770 56 64) (extract v_9773 56 64)) (concat (add (extract v_9770 64 72) (extract v_9773 64 72)) (concat (add (extract v_9770 72 80) (extract v_9773 72 80)) (concat (add (extract v_9770 80 88) (extract v_9773 80 88)) (concat (add (extract v_9770 88 96) (extract v_9773 88 96)) (concat (add (extract v_9770 96 104) (extract v_9773 96 104)) (concat (add (extract v_9770 104 112) (extract v_9773 104 112)) (concat (add (extract v_9770 112 120) (extract v_9773 112 120)) (add (extract v_9770 120 128) (extract v_9773 120 128)))))))))))))))));
      pure ()
    pat_end
