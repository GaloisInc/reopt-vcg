def vpmovsxbw1 : instruction :=
  definst "vpmovsxbw" $ do
    pattern fun (v_2692 : reg (bv 128)) (v_2693 : reg (bv 128)) => do
      v_5542 <- getRegister v_2692;
      setRegister (lhs.of_reg v_2693) (concat (sext (extract v_5542 64 72) 16) (concat (sext (extract v_5542 72 80) 16) (concat (sext (extract v_5542 80 88) 16) (concat (sext (extract v_5542 88 96) 16) (concat (sext (extract v_5542 96 104) 16) (concat (sext (extract v_5542 104 112) 16) (concat (sext (extract v_5542 112 120) 16) (sext (extract v_5542 120 128) 16))))))));
      pure ()
    pat_end;
    pattern fun (v_2702 : reg (bv 128)) (v_2701 : reg (bv 256)) => do
      v_5571 <- getRegister v_2702;
      setRegister (lhs.of_reg v_2701) (concat (sext (extract v_5571 0 8) 16) (concat (sext (extract v_5571 8 16) 16) (concat (sext (extract v_5571 16 24) 16) (concat (sext (extract v_5571 24 32) 16) (concat (sext (extract v_5571 32 40) 16) (concat (sext (extract v_5571 40 48) 16) (concat (sext (extract v_5571 48 56) 16) (concat (sext (extract v_5571 56 64) 16) (concat (sext (extract v_5571 64 72) 16) (concat (sext (extract v_5571 72 80) 16) (concat (sext (extract v_5571 80 88) 16) (concat (sext (extract v_5571 88 96) 16) (concat (sext (extract v_5571 96 104) 16) (concat (sext (extract v_5571 104 112) 16) (concat (sext (extract v_5571 112 120) 16) (sext (extract v_5571 120 128) 16))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2687 : Mem) (v_2688 : reg (bv 128)) => do
      v_11961 <- evaluateAddress v_2687;
      v_11962 <- load v_11961 8;
      setRegister (lhs.of_reg v_2688) (concat (sext (extract v_11962 0 8) 16) (concat (sext (extract v_11962 8 16) 16) (concat (sext (extract v_11962 16 24) 16) (concat (sext (extract v_11962 24 32) 16) (concat (sext (extract v_11962 32 40) 16) (concat (sext (extract v_11962 40 48) 16) (concat (sext (extract v_11962 48 56) 16) (sext (extract v_11962 56 64) 16))))))));
      pure ()
    pat_end;
    pattern fun (v_2696 : Mem) (v_2697 : reg (bv 256)) => do
      v_11987 <- evaluateAddress v_2696;
      v_11988 <- load v_11987 16;
      setRegister (lhs.of_reg v_2697) (concat (sext (extract v_11988 0 8) 16) (concat (sext (extract v_11988 8 16) 16) (concat (sext (extract v_11988 16 24) 16) (concat (sext (extract v_11988 24 32) 16) (concat (sext (extract v_11988 32 40) 16) (concat (sext (extract v_11988 40 48) 16) (concat (sext (extract v_11988 48 56) 16) (concat (sext (extract v_11988 56 64) 16) (concat (sext (extract v_11988 64 72) 16) (concat (sext (extract v_11988 72 80) 16) (concat (sext (extract v_11988 80 88) 16) (concat (sext (extract v_11988 88 96) 16) (concat (sext (extract v_11988 96 104) 16) (concat (sext (extract v_11988 104 112) 16) (concat (sext (extract v_11988 112 120) 16) (sext (extract v_11988 120 128) 16))))))))))))))));
      pure ()
    pat_end
