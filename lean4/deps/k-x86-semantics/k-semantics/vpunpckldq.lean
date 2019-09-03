def vpunpckldq1 : instruction :=
  definst "vpunpckldq" $ do
    pattern fun (v_2700 : reg (bv 128)) (v_2701 : reg (bv 128)) (v_2702 : reg (bv 128)) => do
      v_6366 <- getRegister v_2700;
      v_6368 <- getRegister v_2701;
      setRegister (lhs.of_reg v_2702) (concat (concat (extract v_6366 64 96) (extract v_6368 64 96)) (concat (extract v_6366 96 128) (extract v_6368 96 128)));
      pure ()
    pat_end;
    pattern fun (v_2711 : reg (bv 256)) (v_2712 : reg (bv 256)) (v_2713 : reg (bv 256)) => do
      v_6381 <- getRegister v_2711;
      v_6383 <- getRegister v_2712;
      setRegister (lhs.of_reg v_2713) (concat (concat (extract v_6381 64 96) (extract v_6383 64 96)) (concat (concat (extract v_6381 96 128) (extract v_6383 96 128)) (concat (concat (extract v_6381 192 224) (extract v_6383 192 224)) (concat (extract v_6381 224 256) (extract v_6383 224 256)))));
      pure ()
    pat_end;
    pattern fun (v_2695 : Mem) (v_2696 : reg (bv 128)) (v_2697 : reg (bv 128)) => do
      v_12789 <- evaluateAddress v_2695;
      v_12790 <- load v_12789 16;
      v_12792 <- getRegister v_2696;
      setRegister (lhs.of_reg v_2697) (concat (concat (extract v_12790 64 96) (extract v_12792 64 96)) (concat (extract v_12790 96 128) (extract v_12792 96 128)));
      pure ()
    pat_end;
    pattern fun (v_2706 : Mem) (v_2707 : reg (bv 256)) (v_2708 : reg (bv 256)) => do
      v_12800 <- evaluateAddress v_2706;
      v_12801 <- load v_12800 32;
      v_12803 <- getRegister v_2707;
      setRegister (lhs.of_reg v_2708) (concat (concat (extract v_12801 64 96) (extract v_12803 64 96)) (concat (concat (extract v_12801 96 128) (extract v_12803 96 128)) (concat (concat (extract v_12801 192 224) (extract v_12803 192 224)) (concat (extract v_12801 224 256) (extract v_12803 224 256)))));
      pure ()
    pat_end
