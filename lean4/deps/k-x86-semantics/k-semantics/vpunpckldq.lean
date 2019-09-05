def vpunpckldq1 : instruction :=
  definst "vpunpckldq" $ do
    pattern fun (v_2754 : reg (bv 128)) (v_2755 : reg (bv 128)) (v_2756 : reg (bv 128)) => do
      v_6415 <- getRegister v_2754;
      v_6417 <- getRegister v_2755;
      setRegister (lhs.of_reg v_2756) (concat (concat (extract v_6415 64 96) (extract v_6417 64 96)) (concat (extract v_6415 96 128) (extract v_6417 96 128)));
      pure ()
    pat_end;
    pattern fun (v_2765 : reg (bv 256)) (v_2766 : reg (bv 256)) (v_2767 : reg (bv 256)) => do
      v_6430 <- getRegister v_2765;
      v_6432 <- getRegister v_2766;
      setRegister (lhs.of_reg v_2767) (concat (concat (extract v_6430 64 96) (extract v_6432 64 96)) (concat (concat (extract v_6430 96 128) (extract v_6432 96 128)) (concat (concat (extract v_6430 192 224) (extract v_6432 192 224)) (concat (extract v_6430 224 256) (extract v_6432 224 256)))));
      pure ()
    pat_end;
    pattern fun (v_2748 : Mem) (v_2749 : reg (bv 128)) (v_2750 : reg (bv 128)) => do
      v_12465 <- evaluateAddress v_2748;
      v_12466 <- load v_12465 16;
      v_12468 <- getRegister v_2749;
      setRegister (lhs.of_reg v_2750) (concat (concat (extract v_12466 64 96) (extract v_12468 64 96)) (concat (extract v_12466 96 128) (extract v_12468 96 128)));
      pure ()
    pat_end;
    pattern fun (v_2759 : Mem) (v_2760 : reg (bv 256)) (v_2761 : reg (bv 256)) => do
      v_12476 <- evaluateAddress v_2759;
      v_12477 <- load v_12476 32;
      v_12479 <- getRegister v_2760;
      setRegister (lhs.of_reg v_2761) (concat (concat (extract v_12477 64 96) (extract v_12479 64 96)) (concat (concat (extract v_12477 96 128) (extract v_12479 96 128)) (concat (concat (extract v_12477 192 224) (extract v_12479 192 224)) (concat (extract v_12477 224 256) (extract v_12479 224 256)))));
      pure ()
    pat_end
