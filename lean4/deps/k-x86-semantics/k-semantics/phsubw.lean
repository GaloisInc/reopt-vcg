def phsubw1 : instruction :=
  definst "phsubw" $ do
    pattern fun (v_2573 : reg (bv 128)) (v_2574 : reg (bv 128)) => do
      v_4426 <- getRegister v_2573;
      v_4442 <- getRegister v_2574;
      setRegister (lhs.of_reg v_2574) (concat (concat (concat (concat (concat (concat (concat (sub (extract v_4426 16 32) (extract v_4426 0 16)) (sub (extract v_4426 48 64) (extract v_4426 32 48))) (sub (extract v_4426 80 96) (extract v_4426 64 80))) (sub (extract v_4426 112 128) (extract v_4426 96 112))) (sub (extract v_4442 16 32) (extract v_4442 0 16))) (sub (extract v_4442 48 64) (extract v_4442 32 48))) (sub (extract v_4442 80 96) (extract v_4442 64 80))) (sub (extract v_4442 112 128) (extract v_4442 96 112)));
      pure ()
    pat_end;
    pattern fun (v_2569 : Mem) (v_2570 : reg (bv 128)) => do
      v_11317 <- evaluateAddress v_2569;
      v_11318 <- load v_11317 16;
      v_11334 <- getRegister v_2570;
      setRegister (lhs.of_reg v_2570) (concat (concat (concat (concat (concat (concat (concat (sub (extract v_11318 16 32) (extract v_11318 0 16)) (sub (extract v_11318 48 64) (extract v_11318 32 48))) (sub (extract v_11318 80 96) (extract v_11318 64 80))) (sub (extract v_11318 112 128) (extract v_11318 96 112))) (sub (extract v_11334 16 32) (extract v_11334 0 16))) (sub (extract v_11334 48 64) (extract v_11334 32 48))) (sub (extract v_11334 80 96) (extract v_11334 64 80))) (sub (extract v_11334 112 128) (extract v_11334 96 112)));
      pure ()
    pat_end
