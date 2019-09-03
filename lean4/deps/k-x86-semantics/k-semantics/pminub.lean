def pminub1 : instruction :=
  definst "pminub" $ do
    pattern fun (v_2629 : reg (bv 128)) (v_2630 : reg (bv 128)) => do
      v_5242 <- getRegister v_2630;
      v_5243 <- eval (extract v_5242 0 8);
      v_5244 <- getRegister v_2629;
      v_5245 <- eval (extract v_5244 0 8);
      v_5248 <- eval (extract v_5242 8 16);
      v_5249 <- eval (extract v_5244 8 16);
      v_5252 <- eval (extract v_5242 16 24);
      v_5253 <- eval (extract v_5244 16 24);
      v_5256 <- eval (extract v_5242 24 32);
      v_5257 <- eval (extract v_5244 24 32);
      v_5260 <- eval (extract v_5242 32 40);
      v_5261 <- eval (extract v_5244 32 40);
      v_5264 <- eval (extract v_5242 40 48);
      v_5265 <- eval (extract v_5244 40 48);
      v_5268 <- eval (extract v_5242 48 56);
      v_5269 <- eval (extract v_5244 48 56);
      v_5272 <- eval (extract v_5242 56 64);
      v_5273 <- eval (extract v_5244 56 64);
      v_5276 <- eval (extract v_5242 64 72);
      v_5277 <- eval (extract v_5244 64 72);
      v_5280 <- eval (extract v_5242 72 80);
      v_5281 <- eval (extract v_5244 72 80);
      v_5284 <- eval (extract v_5242 80 88);
      v_5285 <- eval (extract v_5244 80 88);
      v_5288 <- eval (extract v_5242 88 96);
      v_5289 <- eval (extract v_5244 88 96);
      v_5292 <- eval (extract v_5242 96 104);
      v_5293 <- eval (extract v_5244 96 104);
      v_5296 <- eval (extract v_5242 104 112);
      v_5297 <- eval (extract v_5244 104 112);
      v_5300 <- eval (extract v_5242 112 120);
      v_5301 <- eval (extract v_5244 112 120);
      v_5304 <- eval (extract v_5242 120 128);
      v_5305 <- eval (extract v_5244 120 128);
      setRegister (lhs.of_reg v_2630) (concat (mux (ult v_5243 v_5245) v_5243 v_5245) (concat (mux (ult v_5248 v_5249) v_5248 v_5249) (concat (mux (ult v_5252 v_5253) v_5252 v_5253) (concat (mux (ult v_5256 v_5257) v_5256 v_5257) (concat (mux (ult v_5260 v_5261) v_5260 v_5261) (concat (mux (ult v_5264 v_5265) v_5264 v_5265) (concat (mux (ult v_5268 v_5269) v_5268 v_5269) (concat (mux (ult v_5272 v_5273) v_5272 v_5273) (concat (mux (ult v_5276 v_5277) v_5276 v_5277) (concat (mux (ult v_5280 v_5281) v_5280 v_5281) (concat (mux (ult v_5284 v_5285) v_5284 v_5285) (concat (mux (ult v_5288 v_5289) v_5288 v_5289) (concat (mux (ult v_5292 v_5293) v_5292 v_5293) (concat (mux (ult v_5296 v_5297) v_5296 v_5297) (concat (mux (ult v_5300 v_5301) v_5300 v_5301) (mux (ult v_5304 v_5305) v_5304 v_5305))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2624 : Mem) (v_2625 : reg (bv 128)) => do
      v_12618 <- getRegister v_2625;
      v_12619 <- eval (extract v_12618 0 8);
      v_12620 <- evaluateAddress v_2624;
      v_12621 <- load v_12620 16;
      v_12622 <- eval (extract v_12621 0 8);
      v_12625 <- eval (extract v_12618 8 16);
      v_12626 <- eval (extract v_12621 8 16);
      v_12629 <- eval (extract v_12618 16 24);
      v_12630 <- eval (extract v_12621 16 24);
      v_12633 <- eval (extract v_12618 24 32);
      v_12634 <- eval (extract v_12621 24 32);
      v_12637 <- eval (extract v_12618 32 40);
      v_12638 <- eval (extract v_12621 32 40);
      v_12641 <- eval (extract v_12618 40 48);
      v_12642 <- eval (extract v_12621 40 48);
      v_12645 <- eval (extract v_12618 48 56);
      v_12646 <- eval (extract v_12621 48 56);
      v_12649 <- eval (extract v_12618 56 64);
      v_12650 <- eval (extract v_12621 56 64);
      v_12653 <- eval (extract v_12618 64 72);
      v_12654 <- eval (extract v_12621 64 72);
      v_12657 <- eval (extract v_12618 72 80);
      v_12658 <- eval (extract v_12621 72 80);
      v_12661 <- eval (extract v_12618 80 88);
      v_12662 <- eval (extract v_12621 80 88);
      v_12665 <- eval (extract v_12618 88 96);
      v_12666 <- eval (extract v_12621 88 96);
      v_12669 <- eval (extract v_12618 96 104);
      v_12670 <- eval (extract v_12621 96 104);
      v_12673 <- eval (extract v_12618 104 112);
      v_12674 <- eval (extract v_12621 104 112);
      v_12677 <- eval (extract v_12618 112 120);
      v_12678 <- eval (extract v_12621 112 120);
      v_12681 <- eval (extract v_12618 120 128);
      v_12682 <- eval (extract v_12621 120 128);
      setRegister (lhs.of_reg v_2625) (concat (mux (ult v_12619 v_12622) v_12619 v_12622) (concat (mux (ult v_12625 v_12626) v_12625 v_12626) (concat (mux (ult v_12629 v_12630) v_12629 v_12630) (concat (mux (ult v_12633 v_12634) v_12633 v_12634) (concat (mux (ult v_12637 v_12638) v_12637 v_12638) (concat (mux (ult v_12641 v_12642) v_12641 v_12642) (concat (mux (ult v_12645 v_12646) v_12645 v_12646) (concat (mux (ult v_12649 v_12650) v_12649 v_12650) (concat (mux (ult v_12653 v_12654) v_12653 v_12654) (concat (mux (ult v_12657 v_12658) v_12657 v_12658) (concat (mux (ult v_12661 v_12662) v_12661 v_12662) (concat (mux (ult v_12665 v_12666) v_12665 v_12666) (concat (mux (ult v_12669 v_12670) v_12669 v_12670) (concat (mux (ult v_12673 v_12674) v_12673 v_12674) (concat (mux (ult v_12677 v_12678) v_12677 v_12678) (mux (ult v_12681 v_12682) v_12681 v_12682))))))))))))))));
      pure ()
    pat_end
